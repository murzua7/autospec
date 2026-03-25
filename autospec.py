"""
autospec -- Self-Supervising Formal Verification Loop

The main orchestrator, analogous to the agentic loop in Karpathy's autoresearch.
An LLM agent iteratively writes TLA+ specs and fixes code, using the TLC model
checker as a fixed evaluator that cannot be gamed.

Architecture:
  program.md   -> strategy document (human-curated, guides the agent)
  prepare.py   -> IMMUTABLE evaluator (TLC harness, result parser)
  autospec.py  -> THIS FILE: loop orchestrator + agent integration
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
import time
from datetime import datetime
from pathlib import Path
from typing import Any

from prepare import (
    TLCResult,
    TSV_HEADER,
    evaluate_spec_quality,
    format_result_for_agent,
    format_result_tsv,
    run_tlc,
    self_hash,
)

# -- Configuration ------------------------------------------------------

ROOT = Path(__file__).resolve().parent
SPECS_DIR = ROOT / "specs"
MAPPINGS_DIR = ROOT / "mappings"
TRACES_DIR = ROOT / "traces"
RESULTS_FILE = ROOT / "results.tsv"
PROGRAM_FILE = ROOT / "program.md"
PREPARE_FILE = ROOT / "prepare.py"

MAX_ITERATIONS = 1000
TIMEOUT_PER_CHECK = 300
MAX_AGENT_TOKENS = 16384
BRANCH_PREFIX = "autospec"
DEFAULT_MODEL = "claude-sonnet-4-20250514"

# File-queue directories for manual/Claude Code mode
QUEUE_DIR = ROOT / "llm_queue"
QUEUE_REQUESTS = QUEUE_DIR / "requests"
QUEUE_RESPONSES = QUEUE_DIR / "responses"

# Sentinel for "no baseline established yet" (avoids float/int mixing)
_NO_BASELINE = -1

# Record prepare.py hash at import time -- verified each iteration
_PREPARE_HASH = self_hash()


# -- Mapping Management -------------------------------------------------

def load_mapping() -> dict[str, Any]:
    """Load the code->spec mapping from mappings/mapping.json."""
    path = MAPPINGS_DIR / "mapping.json"
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {"modules": []}


def save_mapping(mapping: dict[str, Any]) -> None:
    path = MAPPINGS_DIR / "mapping.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(mapping, indent=2), encoding="utf-8")


def get_target_files(target_dir: Path) -> list[Path]:
    """Discover Python files in the target directory, sorted by size (largest first).

    Largest-first ensures the context gatherer shows substantive modules
    (simulation.py, config.py) rather than empty __init__.py stubs.
    """
    files = sorted(
        target_dir.rglob("*.py"),
        key=lambda p: p.stat().st_size,
        reverse=True,
    )
    # Filter out __pycache__, .venv, test files, etc.
    return [
        f for f in files
        if not any(
            part.startswith(".") or part == "__pycache__" or part == "venv"
            for part in f.parts
        )
    ]


# -- Context Gathering --------------------------------------------------

def gather_context(
    target_dir: Path,
    mapping: dict[str, Any],
    previous_results: list[str],
    current_specs: dict[str, str],
    focus_module: str | None = None,
) -> str:
    """
    Assemble context for the LLM agent:
    - Target code (the module to verify)
    - Existing specs
    - Previous TLC results
    - Mapping state
    """
    sections: list[str] = []

    # 1. Previous results (last 10)
    if previous_results:
        sections.append("## Previous Results (last 10)")
        sections.append(TSV_HEADER)
        for line in previous_results[-10:]:
            sections.append(line)

    # 2. Current mapping
    sections.append("\n## Module Mapping")
    sections.append(json.dumps(mapping, indent=2))

    # 3. Target code
    sections.append("\n## Target Code")
    if focus_module:
        target_path = target_dir / focus_module
        if target_path.exists():
            code = target_path.read_text(errors="replace")
            sections.append(f"### {focus_module}")
            sections.append(f"```python\n{code[:8000]}\n```")
    else:
        # Show largest target files (skip trivial stubs < 50 bytes)
        shown = 0
        for f in get_target_files(target_dir):
            if shown >= 5:
                break
            if f.stat().st_size < 50:
                continue
            rel = f.relative_to(target_dir)
            code = f.read_text(errors="replace")
            sections.append(f"### {rel}")
            sections.append(f"```python\n{code[:4000]}\n```")
            shown += 1

    # 4. Existing specs
    if current_specs:
        sections.append("\n## Existing TLA+ Specs")
        for name, content in current_specs.items():
            sections.append(f"### {name}")
            sections.append(f"```tla\n{content}\n```")

    return "\n".join(sections)


def load_current_specs() -> dict[str, str]:
    """Load all .tla files from specs/ directory (excluding TLC trace artifacts)."""
    specs: dict[str, str] = {}
    if SPECS_DIR.exists():
        for f in SPECS_DIR.glob("*.tla"):
            if "_TTrace_" in f.name:
                continue
            specs[f.name] = f.read_text(errors="replace")
    return specs


def load_previous_results() -> list[str]:
    """Load results.tsv lines."""
    if RESULTS_FILE.exists():
        lines = RESULTS_FILE.read_text(encoding="utf-8").strip().split("\n")
        return lines[1:] if len(lines) > 1 else []  # Skip header
    return []


# -- Agent Integration --------------------------------------------------

def build_system_prompt() -> str:
    """Build the system prompt from program.md."""
    program = PROGRAM_FILE.read_text(encoding="utf-8")
    return textwrap.dedent(f"""\
        You are the autospec formal verification agent.
        Follow the instructions in program.md EXACTLY.

        <program>
        {program}
        </program>

        ## Response Format

        You MUST respond with a JSON object containing your actions:

        ```json
        {{
            "summary": "Brief description of what you did this iteration",
            "classification": "NEW_SPEC | SPEC_REFINE | BUG_FIX | ABSTRACTION",
            "focus_module": "path/to/module.py",
            "files": {{
                "specs/ModuleName.tla": "full TLA+ spec content",
                "specs/ModuleName.cfg": "full config content",
                "target/example/module.py": "fixed code (only if BUG_FIX)"
            }},
            "delete_specs": ["OldSpec.tla"],
            "reasoning": "Why you made these changes, what you expect TLC to find",
            "next_focus": "What to focus on next iteration"
        }}
        ```

        IMPORTANT:
        - The "files" dict contains COMPLETE file contents (not diffs)
        - Only include files you are creating or modifying
        - NEVER include prepare.py in "files"
        - Spec files go in specs/ directory
        - Code fixes go in the target directory
        - Use "delete_specs" to remove obsolete specs (both .tla and .cfg are deleted)
    """)


def call_agent(
    context: str,
    tlc_feedback: str | None,
    model: str = DEFAULT_MODEL,
    mode: str = "queue",
) -> dict[str, Any]:
    """
    Call the LLM agent with context and TLC feedback.
    Returns parsed JSON with the agent's actions.

    Modes:
      - "queue": File-based queue (default). Writes prompt to llm_queue/requests/,
        waits for response in llm_queue/responses/. Works with Claude Code Max
        or any external LLM process.
      - "api": Direct Anthropic API call (requires ANTHROPIC_API_KEY with credits).
    """
    user_content = "## Current State\n\n" + context
    if tlc_feedback:
        user_content += "\n\n## TLC Feedback From Last Iteration\n\n" + tlc_feedback
    else:
        user_content += (
            "\n\n## Instructions\n\n"
            "This is the first iteration. Examine the target code and write "
            "your first TLA+ specification. Start simple: model the core "
            "state machine and add a TypeOK invariant."
        )

    system_prompt = build_system_prompt()

    if mode == "api":
        return _call_agent_api(system_prompt, user_content, model)
    else:
        return _call_agent_queue(system_prompt, user_content)


def _call_agent_api(
    system_prompt: str,
    user_content: str,
    model: str,
) -> dict[str, Any]:
    """Direct Anthropic API call (requires credits)."""
    import anthropic

    client = anthropic.Anthropic()

    messages = [{"role": "user", "content": user_content}]

    response = client.messages.create(
        model=model,
        max_tokens=MAX_AGENT_TOKENS,
        system=system_prompt,
        messages=messages,
    )

    text = ""
    for block in response.content:
        if block.type == "text":
            text += block.text

    return _parse_agent_response(text)


def _call_agent_queue(
    system_prompt: str,
    user_content: str,
    timeout: int = 600,
    poll_interval: float = 2.0,
) -> dict[str, Any]:
    """File-queue mode: write prompt, wait for response.

    A separate process (Claude Code session, Ollama script, etc.) reads
    from llm_queue/requests/ and writes to llm_queue/responses/.
    """
    import uuid as _uuid

    QUEUE_REQUESTS.mkdir(parents=True, exist_ok=True)
    QUEUE_RESPONSES.mkdir(parents=True, exist_ok=True)

    request_id = str(_uuid.uuid4())[:12]
    request_file = QUEUE_REQUESTS / f"{request_id}.json"
    response_file = QUEUE_RESPONSES / f"{request_id}.json"

    # Write request
    request_data = {
        "id": request_id,
        "system": system_prompt,
        "user": user_content,
        "timestamp": datetime.now().isoformat(),
    }
    request_file.write_text(json.dumps(request_data, indent=2), encoding="utf-8")
    print(f"  [queue] Request written: {request_file.name}")
    print(f"  [queue] Waiting for response at: {response_file.name}")
    print(f"  [queue] (Run /autospec-respond or process the queue externally)")

    # Poll for response
    elapsed = 0.0
    while elapsed < timeout:
        if response_file.exists():
            try:
                text = response_file.read_text(encoding="utf-8")
                result = _parse_agent_response(text)
                # Clean up
                request_file.unlink(missing_ok=True)
                response_file.unlink(missing_ok=True)
                return result
            except (json.JSONDecodeError, ValueError):
                # Partial write, wait more
                pass
        time.sleep(poll_interval)
        elapsed += poll_interval
        if int(elapsed) % 30 == 0 and elapsed > 0:
            print(f"  [queue] Still waiting... ({int(elapsed)}s)")

    # Timeout
    request_file.unlink(missing_ok=True)
    raise TimeoutError(
        f"No response after {timeout}s. Ensure a queue processor is running."
    )


def _parse_agent_response(text: str) -> dict[str, Any]:
    """Extract JSON from the agent's response text."""
    import re

    # Try to find JSON block in markdown code fence
    json_match = re.search(r"```json\s*\n(.*?)\n\s*```", text, re.DOTALL)
    if json_match:
        try:
            return json.loads(json_match.group(1))
        except json.JSONDecodeError:
            pass

    # Try to find raw JSON object
    # Find the outermost { ... }
    brace_depth = 0
    start = -1
    for i, ch in enumerate(text):
        if ch == "{":
            if brace_depth == 0:
                start = i
            brace_depth += 1
        elif ch == "}":
            brace_depth -= 1
            if brace_depth == 0 and start >= 0:
                try:
                    return json.loads(text[start : i + 1])
                except json.JSONDecodeError:
                    start = -1

    # Fallback: return as error
    return {
        "summary": "Agent response could not be parsed as JSON",
        "classification": "ERROR",
        "files": {},
        "reasoning": text[:2000],
        "next_focus": "",
        "focus_module": "",
    }


# -- File Application ---------------------------------------------------

def apply_changes(agent_output: dict[str, Any]) -> list[str]:
    """
    Write files from the agent's output to disk.
    Returns list of files written.

    Security: path traversal prevention + allowlist enforcement.
    The agent can only write to specs/, mappings/, and target/ directories.
    The agent can request spec deletion via "delete_specs": ["name.tla", ...].
    """
    files_written: list[str] = []

    # Handle spec deletions (agent can only delete from specs/)
    for name in agent_output.get("delete_specs", []):
        if "/" in name or "\\" in name or ".." in name:
            print(f"  BLOCKED: invalid delete_specs name: {name}")
            continue
        for ext in ("", ".cfg"):
            target = SPECS_DIR / (name + ext) if ext else SPECS_DIR / name
            if target.exists() and target.is_file():
                target.unlink()
                print(f"  -> Deleted {target.name}")
                files_written.append(f"specs/{target.name}")
        # Also clean any trace files for this spec
        stem = Path(name).stem
        for trace in SPECS_DIR.glob(f"{stem}_TTrace_*"):
            trace.unlink()

    files_dict = agent_output.get("files", {})

    # Allowed write directories (relative to ROOT)
    ALLOWED_PREFIXES = ("specs/", "mappings/", "target/")
    # Files that must never be modified by the agent
    FORBIDDEN_NAMES = {"prepare.py", "autospec.py", "__main__.py", "program.md", "pyproject.toml"}

    for rel_path, content in files_dict.items():
        # Resolve and verify the path stays within ROOT (path traversal defense)
        full_path = (ROOT / rel_path).resolve()
        if not full_path.is_relative_to(ROOT):
            print(f"  BLOCKED: path escapes project root: {rel_path}")
            continue

        # Block forbidden files by name
        if full_path.name in FORBIDDEN_NAMES:
            print(f"  BLOCKED: agent attempted to modify protected file: {rel_path}")
            continue

        # Enforce directory allowlist
        rel_resolved = full_path.relative_to(ROOT).as_posix()
        if not any(rel_resolved.startswith(p) for p in ALLOWED_PREFIXES):
            print(f"  BLOCKED: path not in allowed directories: {rel_path}")
            continue

        full_path.parent.mkdir(parents=True, exist_ok=True)
        full_path.write_text(content, encoding="utf-8")
        files_written.append(rel_path)
        print(f"  -> Wrote {rel_path} ({len(content)} chars)")

    return files_written


# -- Git Operations -----------------------------------------------------

def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    """Run a git command in the project root."""
    return subprocess.run(
        ["git"] + list(args),
        capture_output=True,
        text=True,
        cwd=str(ROOT),
        check=check,
        timeout=30,
    )


def ensure_git_repo() -> None:
    """Initialize git repo if not already one."""
    if not (ROOT / ".git").exists():
        git("init")
        git("add", "-A")
        git("commit", "-m", "autospec: initial project structure")


def create_branch(tag: str = "") -> str:
    """Create and checkout a new autospec branch."""
    ts = datetime.now().strftime("%Y%m%d-%H%M")
    branch = f"{BRANCH_PREFIX}/{ts}"
    if tag:
        branch += f"-{tag}"
    git("checkout", "-b", branch)
    return branch


def commit_changes(message: str, files: list[str]) -> bool:
    """Stage specific files and commit. Returns True if commit succeeded."""
    if not files:
        return False
    for f in files:
        git("add", f)
    result = git("commit", "-m", message, check=False)
    return result.returncode == 0


def revert_last_commit() -> None:
    """Revert the last commit (like autoresearch's git reset on regression)."""
    git("reset", "--hard", "HEAD~1")


# -- TLC Evaluation -----------------------------------------------------

def evaluate_all_specs() -> tuple[int, list[TLCResult]]:
    """
    Run TLC on all specs in specs/ directory.
    Returns (total_violations, list_of_results).

    Anti-reward-hacking: penalizes trivial specs that pass with 0 states
    explored (empty spec or cfg with no invariants).
    """
    total_violations = 0
    results: list[TLCResult] = []

    if not SPECS_DIR.exists():
        return 0, []

    for tla_file in sorted(SPECS_DIR.glob("*.tla")):
        if "_TTrace_" in tla_file.name:
            continue
        cfg_file = tla_file.with_suffix(".cfg")
        if not cfg_file.exists():
            continue

        # Anti-reward-hacking: verify cfg declares at least one INVARIANT
        cfg_text = cfg_file.read_text(encoding="utf-8")
        if "INVARIANT" not in cfg_text and "PROPERTY" not in cfg_text:
            total_violations += 1  # Penalize empty configs
            result = TLCResult(
                spec_file=str(tla_file),
                config_file=str(cfg_file),
                error_message="Config declares no INVARIANT or PROPERTY -- trivial spec rejected",
            )
            results.append(result)
            continue

        result = run_tlc(tla_file, cfg_file, timeout=TIMEOUT_PER_CHECK)
        total_violations += result.violation_count
        # Count parse errors as violations (spec is broken)
        if result.parse_errors:
            total_violations += len(result.parse_errors)
        # Penalize trivial passes (0 states explored = empty/broken spec)
        if result.passed and result.distinct_states == 0:
            total_violations += 1
        results.append(result)

    return total_violations, results


# -- Integrity Check ----------------------------------------------------

def verify_evaluator_integrity() -> bool:
    """Verify prepare.py hasn't been modified since autospec started."""
    current = self_hash()
    if current != _PREPARE_HASH:
        print("==================================================")
        print("|  ! INTEGRITY VIOLATION: prepare.py modified  |")
        print("|  The fixed evaluator has been tampered with.  |")
        print("|  Aborting to prevent reward hacking.          |")
        print("==================================================")
        return False
    return True


# -- Main Loop ----------------------------------------------------------

def _normalize_path(p: str | Path) -> Path:
    """Normalize MSYS/Git Bash paths (/c/Users/...) to native Windows paths."""
    s = str(p)
    if sys.platform == "win32" and len(s) >= 3 and s[0] == "/" and s[2] == "/":
        # /c/Users/... -> C:/Users/...
        s = s[1].upper() + ":" + s[2:]
    return Path(s)


def run_loop(
    target_dir: str | Path,
    model: str = DEFAULT_MODEL,
    max_iterations: int = MAX_ITERATIONS,
    tag: str = "",
    mode: str = "queue",
) -> None:
    """
    The autoresearch-style self-supervising loop.

    1. Agent reads code + existing specs + previous results
    2. Agent writes/refines TLA+ spec (or fixes code)
    3. prepare.py runs TLC (FIXED EVALUATOR)
    4. Accept if violations decrease; revert if they increase
    5. Log to results.tsv
    6. NEVER STOP (until max_iterations)
    """
    target_dir = _normalize_path(target_dir).resolve()
    if not target_dir.exists():
        print(f"Error: target directory not found: {target_dir}")
        sys.exit(1)

    print("=" * 50)
    print("  autospec -- Formal Verification")
    print("  Self-Supervising TLA+ Verification Loop")
    print("=" * 50)
    print(f"  Target:     {target_dir}")
    print(f"  Mode:       {mode}")
    print(f"  Model:      {model if mode == 'api' else 'N/A (queue mode)'}")
    print(f"  Max iters:  {max_iterations}")
    print(f"  Evaluator:  prepare.py (SHA256: {_PREPARE_HASH[:16]}...)")
    print()

    # Initialize
    ensure_git_repo()
    branch = create_branch(tag)
    print(f"  Branch:     {branch}")

    SPECS_DIR.mkdir(parents=True, exist_ok=True)
    TRACES_DIR.mkdir(parents=True, exist_ok=True)

    # Clean stale artifacts from previous targets.
    # If the mapping references files from a different target, wipe everything
    # so old specs don't pollute the violation count.
    old_mapping = load_mapping()
    if old_mapping.get("modules"):
        old_paths = {m.get("code_path", "") for m in old_mapping["modules"]}
        new_paths = {str(f.relative_to(target_dir)) for f in get_target_files(target_dir)}
        if old_paths and not old_paths & new_paths:
            print("  Detected target change -- cleaning stale specs and results")
            import shutil
            for f in SPECS_DIR.iterdir():
                f.unlink()
            if TRACES_DIR.exists():
                shutil.rmtree(TRACES_DIR)
                TRACES_DIR.mkdir(parents=True, exist_ok=True)
            RESULTS_FILE.unlink(missing_ok=True)
            (MAPPINGS_DIR / "mapping.json").unlink(missing_ok=True)
            # Clean queue
            for d in (QUEUE_REQUESTS, QUEUE_RESPONSES):
                if d.exists():
                    for f in d.iterdir():
                        f.unlink()

    # Initialize results.tsv
    if not RESULTS_FILE.exists():
        RESULTS_FILE.write_text(TSV_HEADER + "\n", encoding="utf-8")

    # Initialize mapping
    mapping = load_mapping()
    if not mapping.get("modules"):
        target_files = get_target_files(target_dir)
        mapping["modules"] = [
            {
                "code_path": str(f.relative_to(target_dir)),
                "spec_file": None,
                "status": "pending",
            }
            for f in target_files
        ]
        save_mapping(mapping)

    # Baseline evaluation
    print("\n-- Baseline Evaluation --")
    best_violations, baseline_results = evaluate_all_specs()
    if baseline_results:
        for r in baseline_results:
            print(format_result_for_agent(r))
    else:
        print("  No specs yet -- agent will create the first one.")
        best_violations = _NO_BASELINE

    # Log baseline
    baseline_tsv = format_result_tsv(
        0,
        baseline_results[0] if baseline_results else TLCResult(spec_file="none", config_file="none"),
        "BASELINE",
        "Initial state",
    )
    with open(RESULTS_FILE, "a", encoding="utf-8") as f:
        f.write(baseline_tsv + "\n")

    # -- Main Loop --------------------------------------------------
    tlc_feedback: str | None = None
    focus_module: str | None = None
    consecutive_errors = 0

    for iteration in range(1, max_iterations + 1):
        print(f"\n{'-' * 60}")
        print(f"  Iteration {iteration}/{max_iterations}")
        print(f"  Best violations: {best_violations}")
        print(f"{'-' * 60}")

        # Integrity check
        if not verify_evaluator_integrity():
            revert_last_commit()
            print("  Reverted last commit and aborting.")
            break

        # Gather context
        context = gather_context(
            target_dir=target_dir,
            mapping=mapping,
            previous_results=load_previous_results(),
            current_specs=load_current_specs(),
            focus_module=focus_module,
        )

        # Call agent
        print("  Calling agent...")
        try:
            agent_output = call_agent(context, tlc_feedback, model=model, mode=mode)
        except Exception as e:
            print(f"  ! Agent error: {e}")
            consecutive_errors += 1
            if consecutive_errors >= 3:
                print("  Too many consecutive agent errors. Stopping.")
                break
            continue

        consecutive_errors = 0
        summary = agent_output.get("summary", "no summary")
        classification = agent_output.get("classification", "UNKNOWN")
        focus_module = agent_output.get("next_focus") or agent_output.get("focus_module")

        print(f"  Classification: {classification}")
        print(f"  Summary: {summary}")

        # Apply changes
        files_written = apply_changes(agent_output)
        if not files_written:
            print("  ! Agent produced no file changes. Continuing.")
            tlc_feedback = "You produced no file changes. Please write a TLA+ spec."
            continue

        # Commit
        commit_msg = f"autospec iter {iteration} [{classification}]: {summary}"
        committed = commit_changes(commit_msg, files_written)
        if not committed:
            print("  ! Nothing to commit (no changes detected).")

        # Run TLC (FIXED EVALUATOR)
        # Second integrity check: verify evaluator right before the trust boundary.
        # TLC found (IntegrityCheck spec) that a gap between apply_changes() and
        # evaluate_all_specs() could allow a compromised evaluator to run.
        if not verify_evaluator_integrity():
            revert_last_commit()
            print("  Integrity violation detected before evaluation. Aborting.")
            break
        print("  Running TLC model checker...")
        current_violations, results = evaluate_all_specs()

        # Build feedback for next iteration
        feedback_parts: list[str] = []
        for r in results:
            feedback_parts.append(format_result_for_agent(r))
        tlc_feedback = "\n\n".join(feedback_parts) if feedback_parts else None

        # Print results
        for r in results:
            status = "PASS OK" if r.passed else f"FAIL FAIL ({r.violation_count} violations)"
            print(f"  {Path(r.spec_file).name}: {status} "
                  f"({r.distinct_states} states, {r.time_seconds:.1f}s)")

        # Save traces for violations
        for r in results:
            for v in r.violations:
                if v.trace:
                    trace_file = TRACES_DIR / f"iter{iteration}_{v.property_name}.json"
                    trace_data = [
                        {
                            "step": s.step_number,
                            "description": s.state_description,
                            "variables": s.variables,
                        }
                        for s in v.trace
                    ]
                    trace_file.write_text(json.dumps(trace_data, indent=2), encoding="utf-8")

        # -- Accept / Reject Gate ----------------------------------
        if current_violations == 0 and results:
            # Perfect score -- all specs pass
            action = "CLEAN"
            print(f"  * ZERO VIOLATIONS -- all specs verified!")
            best_violations = 0

        elif best_violations == _NO_BASELINE:
            # First spec ever -- always accept
            action = "FIRST"
            best_violations = current_violations
            print(f"  First spec: {current_violations} violations (baseline set)")

        elif current_violations < best_violations:
            # Improvement -- keep
            action = "KEEP"
            print(f"  OK Improved: {best_violations} -> {current_violations} violations")
            best_violations = current_violations

        elif current_violations == best_violations:
            # No change -- keep (spec might have been refined without changing count)
            action = "KEEP_EQUAL"
            print(f"  ~ No change: {current_violations} violations")

        else:
            # Regression -- revert
            action = "DISCARD"
            print(f"  FAIL Regressed: {best_violations} -> {current_violations} violations")
            print(f"    Reverting commit...")
            if committed:
                revert_last_commit()

        # Log to results.tsv
        log_result = results[0] if results else TLCResult(spec_file="none", config_file="none")
        tsv_line = format_result_tsv(iteration, log_result, action, summary)
        with open(RESULTS_FILE, "a", encoding="utf-8") as f:
            f.write(tsv_line + "\n")

        # Update mapping status
        if agent_output.get("focus_module"):
            for mod in mapping.get("modules", []):
                if mod["code_path"] == agent_output["focus_module"]:
                    if current_violations == 0:
                        mod["status"] = "verified"
                    elif action in ("KEEP", "FIRST", "KEEP_EQUAL"):
                        mod["status"] = "in_progress"
                    break
            save_mapping(mapping)

        # Check if all modules verified
        all_verified = all(
            m.get("status") == "verified"
            for m in mapping.get("modules", [])
        )
        if all_verified and mapping.get("modules"):
            print("\n==================================================")
            print("|  * ALL MODULES VERIFIED -- autospec complete   |")
            print("==================================================")
            break

    # Final summary
    print(f"\n{'=' * 60}")
    print(f"  autospec completed after {iteration} iterations")
    print(f"  Final violations: {best_violations}")
    print(f"  Branch: {branch}")
    print(f"  Results: {RESULTS_FILE}")
    print(f"{'=' * 60}")
