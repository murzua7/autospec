"""
IMMUTABLE EVALUATOR -- The agent must NEVER modify this file.

This is the TLC model checker harness -- the fixed evaluator in the
autospec loop, analogous to prepare.py in Karpathy's autoresearch.

The TLC model checker is mathematically exhaustive: it explores every
reachable state in the specification's state space. It cannot be gamed.
Counterexample traces provide structured feedback far richer than a scalar.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

# -- Constants ----------------------------------------------------------

ROOT = Path(__file__).resolve().parent
TLA2TOOLS_JAR = ROOT / "lib" / "tla2tools.jar"
TLA2TOOLS_URL = (
    "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/"
    "tla2tools.jar"
)
DEFAULT_TIMEOUT = 300  # 5 minutes, matching autoresearch's budget
JAVA_CMD = "java"

# Hash of THIS file -- used by autospec.py to verify immutability
def self_hash() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


# -- Data Structures ----------------------------------------------------

@dataclass
class TraceStep:
    """One state in a TLC counterexample trace."""
    step_number: int
    state_description: str
    variables: dict[str, str] = field(default_factory=dict)


@dataclass
class Violation:
    """A single invariant/property violation found by TLC."""
    violation_type: str          # "invariant", "deadlock", "liveness", "assertion"
    property_name: str           # Which invariant/property failed
    trace: list[TraceStep] = field(default_factory=list)
    raw_message: str = ""


@dataclass
class TLCResult:
    """Complete result of a TLC model-checking run."""
    spec_file: str
    config_file: str
    # Outcome
    passed: bool = False
    violations: list[Violation] = field(default_factory=list)
    # Counts
    violation_count: int = 0
    invariant_violations: int = 0
    deadlocks: int = 0
    liveness_failures: int = 0
    assertion_failures: int = 0
    # State space
    states_found: int = 0
    distinct_states: int = 0
    queue_size: int = 0
    # Timing
    time_seconds: float = 0.0
    # Raw
    raw_output: str = ""
    exit_code: int = -1
    error_message: str = ""
    # Parse errors (spec syntax issues)
    parse_errors: list[str] = field(default_factory=list)


@dataclass
class SpecQuality:
    """Quality metrics for a specification + TLC result."""
    spec_file: str
    violation_count: int         # Primary fitness signal (lower = better)
    states_explored: int
    distinct_states: int
    invariant_count: int         # How many invariants are defined
    temporal_count: int          # How many temporal properties defined
    spec_lines: int              # Spec complexity
    check_time: float            # Seconds
    passed: bool
    trace_max_depth: int         # Longest counterexample trace


# -- TLC Runner ---------------------------------------------------------

def ensure_tlc() -> Path:
    """Download tla2tools.jar if not present. Returns path to jar."""
    if TLA2TOOLS_JAR.exists():
        return TLA2TOOLS_JAR
    TLA2TOOLS_JAR.parent.mkdir(parents=True, exist_ok=True)
    print(f"[prepare] Downloading tla2tools.jar -> {TLA2TOOLS_JAR}")
    urllib.request.urlretrieve(TLA2TOOLS_URL, TLA2TOOLS_JAR)
    print(f"[prepare] Downloaded ({TLA2TOOLS_JAR.stat().st_size / 1e6:.1f} MB)")
    return TLA2TOOLS_JAR


def _check_java() -> bool:
    """Verify Java is available."""
    try:
        r = subprocess.run(
            [JAVA_CMD, "-version"],
            capture_output=True, text=True, timeout=10,
        )
        return r.returncode == 0
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False


def run_tlc(
    spec_path: str | Path,
    config_path: str | Path | None = None,
    timeout: int = DEFAULT_TIMEOUT,
    workers: int = 0,  # 0 = auto (number of cores)
    jvm_args: list[str] | None = None,
) -> TLCResult:
    """
    Run the TLC model checker on a TLA+ specification.

    This is the FIXED EVALUATOR -- like val_bpb in autoresearch.
    It explores the entire reachable state space and returns structured
    results including counterexample traces for every violation.

    Args:
        spec_path: Path to the .tla specification file
        config_path: Path to .cfg file (defaults to spec_path with .cfg extension)
        timeout: Maximum seconds for TLC to run
        workers: Number of TLC worker threads (0 = auto)
        jvm_args: Additional JVM arguments

    Returns:
        TLCResult with all violations, traces, state counts, and timing
    """
    spec_path = Path(spec_path).resolve()
    if not spec_path.exists():
        return TLCResult(
            spec_file=str(spec_path),
            config_file="",
            error_message=f"Spec file not found: {spec_path}",
        )

    if config_path is None:
        config_path = spec_path.with_suffix(".cfg")
    config_path = Path(config_path).resolve()

    if not config_path.exists():
        return TLCResult(
            spec_file=str(spec_path),
            config_file=str(config_path),
            error_message=f"Config file not found: {config_path}",
        )

    jar = ensure_tlc()
    if not _check_java():
        return TLCResult(
            spec_file=str(spec_path),
            config_file=str(config_path),
            error_message="Java not found. TLC requires a JRE.",
        )

    # Build command -- use filenames only since we cwd to spec_path.parent
    # TLC requires the module name to match the filename, so we must run
    # from the spec's directory and pass just the filename.
    jvm = jvm_args or ["-XX:+UseParallelGC", "-Xmx4g"]
    cmd = [JAVA_CMD] + jvm + [
        "-jar", str(jar),
        "-config", config_path.name,
        "-cleanup",      # Remove states directory after checking
        "-deadlock",      # Check for deadlocks
    ]
    if workers > 0:
        cmd.extend(["-workers", str(workers)])
    else:
        cmd.extend(["-workers", "auto"])
    cmd.append(spec_path.name)

    # Run TLC
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(spec_path.parent),
        )
        elapsed = time.monotonic() - start
        raw = proc.stdout + "\n" + proc.stderr
        result = parse_tlc_output(raw, str(spec_path), str(config_path))
        result.time_seconds = elapsed
        result.exit_code = proc.returncode
        return result
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return TLCResult(
            spec_file=str(spec_path),
            config_file=str(config_path),
            time_seconds=elapsed,
            error_message=f"TLC timed out after {timeout}s. Reduce state space.",
        )
    except Exception as e:
        elapsed = time.monotonic() - start
        return TLCResult(
            spec_file=str(spec_path),
            config_file=str(config_path),
            time_seconds=elapsed,
            error_message=f"TLC execution error: {e}",
        )


# -- TLC Output Parser -------------------------------------------------

def parse_tlc_output(
    raw: str, spec_file: str, config_file: str
) -> TLCResult:
    """
    Parse TLC's stdout/stderr into a structured TLCResult.

    TLC output format is complex but follows patterns:
    - State statistics in "X states generated, Y distinct states found"
    - Violations start with "Error:" or "Invariant ... is violated"
    - Traces are sequences of "State N: <description>" blocks
    - Parse errors contain "***" or "Parsing error"
    """
    result = TLCResult(spec_file=spec_file, config_file=config_file, raw_output=raw)

    # -- Check for parse/syntax errors --
    parse_error_patterns = [
        r"^\*\*\* Errors?: (.+)$",
        r"^Semantic error[s]?.*:\s*(.+)$",
        r"^Parsing error:\s*(.+)$",
        r"^Could not parse module (.+)$",
        r"^TLC threw an unexpected exception.*$",
        r"^Unknown operator: (.+)$",
        r"^Was expecting .+$",
    ]
    for pattern in parse_error_patterns:
        for match in re.finditer(pattern, raw, re.MULTILINE):
            result.parse_errors.append(match.group(0).strip())

    # -- Extract state statistics --
    m = re.search(
        r"(\d+)\s+states\s+generated,\s+(\d+)\s+distinct\s+states\s+found",
        raw,
    )
    if m:
        result.states_found = int(m.group(1))
        result.distinct_states = int(m.group(2))

    m = re.search(r"(\d+)\s+states\s+left\s+on\s+queue", raw)
    if m:
        result.queue_size = int(m.group(1))

    # -- Detect violations --
    violations: list[Violation] = []

    # Invariant violations
    inv_pattern = r"(?:Error:\s*)?Invariant\s+(\w+)\s+is\s+violated"
    for m in re.finditer(inv_pattern, raw):
        v = Violation(
            violation_type="invariant",
            property_name=m.group(1),
            raw_message=m.group(0),
        )
        violations.append(v)
        result.invariant_violations += 1

    # Assertion failures
    assert_pattern = r"(?:Error:\s*)?(?:The\s+first\s+)?assertion.*(?:line\s+(\d+))?.*failed"
    for m in re.finditer(assert_pattern, raw, re.IGNORECASE):
        v = Violation(
            violation_type="assertion",
            property_name=f"assertion_line_{m.group(1) or 'unknown'}",
            raw_message=m.group(0),
        )
        violations.append(v)
        result.assertion_failures += 1

    # Deadlock
    deadlock_pattern = r"(?:Error:\s*)?Temporal properties were violated|(?:Error:\s*)?Deadlock\s+reached"
    for m in re.finditer(r"(?:Error:\s*)?Deadlock\s+reached", raw):
        v = Violation(
            violation_type="deadlock",
            property_name="Deadlock",
            raw_message=m.group(0),
        )
        violations.append(v)
        result.deadlocks += 1

    # Liveness / temporal property violations
    liveness_pattern = r"(?:Error:\s*)?Temporal\s+properties\s+were\s+violated"
    if re.search(liveness_pattern, raw):
        # Try to extract which property
        prop_m = re.search(r"is\s+violated\s+by\s+the\s+following\s+behavior.*?property\s+(\w+)", raw, re.DOTALL)
        prop_name = prop_m.group(1) if prop_m else "temporal_unknown"
        v = Violation(
            violation_type="liveness",
            property_name=prop_name,
            raw_message="Temporal properties were violated",
        )
        violations.append(v)
        result.liveness_failures += 1

    # -- Parse counterexample traces --
    # TLC outputs traces as:
    # State 1: <Initial predicate>
    # /\ var1 = value1
    # /\ var2 = value2
    # State 2: <Action>
    # ...
    trace_blocks = re.split(r"(?=State\s+\d+:)", raw)
    current_trace: list[TraceStep] = []
    for block in trace_blocks:
        state_m = re.match(r"State\s+(\d+):\s*<?(.*?)>?\s*$", block, re.MULTILINE)
        if not state_m:
            continue
        step_num = int(state_m.group(1))
        desc = state_m.group(2).strip()
        variables: dict[str, str] = {}
        for var_m in re.finditer(r"/\\\s+(\w+)\s*=\s*(.+?)$", block, re.MULTILINE):
            variables[var_m.group(1)] = var_m.group(2).strip()
        step = TraceStep(
            step_number=step_num,
            state_description=desc,
            variables=variables,
        )
        if step_num == 1 and current_trace:
            # New trace starts -- assign previous trace to last violation
            _assign_trace(violations, current_trace)
            current_trace = []
        current_trace.append(step)

    if current_trace:
        _assign_trace(violations, current_trace)

    result.violations = violations
    result.violation_count = len(violations)
    result.passed = (
        len(violations) == 0
        and len(result.parse_errors) == 0
        and result.states_found > 0
    )

    return result


def _assign_trace(violations: list[Violation], trace: list[TraceStep]) -> None:
    """Assign a parsed trace to the most recent violation without one."""
    for v in reversed(violations):
        if not v.trace:
            v.trace = trace
            return


# -- Quality Evaluation -------------------------------------------------

def evaluate_spec_quality(result: TLCResult, spec_path: str | Path) -> SpecQuality:
    """
    Compute quality metrics for a spec + TLC result.

    The violation_count is the primary fitness signal (lower = better),
    analogous to val_bpb in autoresearch.
    """
    spec_path = Path(spec_path)
    spec_text = spec_path.read_text() if spec_path.exists() else ""

    # Count invariants and temporal properties in the spec
    invariant_count = len(re.findall(
        r"^\s*INVARIANT(?:S)?\s+(\w+)", spec_text, re.MULTILINE
    ))
    # Also count inline invariant definitions
    invariant_count += len(re.findall(
        r"^\w+\s*==\s*.*\\in\s+", spec_text, re.MULTILINE
    ))

    temporal_count = len(re.findall(
        r"^\s*PROPERT(?:Y|IES)\s+(\w+)", spec_text, re.MULTILINE
    ))

    # Longest counterexample trace
    trace_max = 0
    for v in result.violations:
        if len(v.trace) > trace_max:
            trace_max = len(v.trace)

    return SpecQuality(
        spec_file=str(spec_path),
        violation_count=result.violation_count,
        states_explored=result.states_found,
        distinct_states=result.distinct_states,
        invariant_count=invariant_count,
        temporal_count=temporal_count,
        spec_lines=spec_text.count("\n") + 1 if spec_text else 0,
        check_time=result.time_seconds,
        passed=result.passed,
        trace_max_depth=trace_max,
    )


# -- Result Formatting --------------------------------------------------

def format_result_for_agent(result: TLCResult) -> str:
    """
    Format TLCResult as structured text for the LLM agent.
    This is the feedback signal -- much richer than a scalar.
    """
    lines: list[str] = []
    lines.append("=" * 60)
    lines.append(f"TLC RESULT: {Path(result.spec_file).name}")
    lines.append("=" * 60)

    if result.error_message:
        lines.append(f"\n! ERROR: {result.error_message}")

    if result.parse_errors:
        lines.append(f"\n! PARSE ERRORS ({len(result.parse_errors)}):")
        for e in result.parse_errors:
            lines.append(f"  * {e}")

    lines.append(f"\nPassed: {'YES OK' if result.passed else 'NO FAIL'}")
    lines.append(f"Violations: {result.violation_count}")
    lines.append(f"  Invariant: {result.invariant_violations}")
    lines.append(f"  Deadlock:  {result.deadlocks}")
    lines.append(f"  Liveness:  {result.liveness_failures}")
    lines.append(f"  Assertion: {result.assertion_failures}")
    lines.append(f"States: {result.states_found} found, {result.distinct_states} distinct")
    lines.append(f"Time: {result.time_seconds:.1f}s")

    for i, v in enumerate(result.violations, 1):
        lines.append(f"\n{'-' * 40}")
        lines.append(f"VIOLATION {i}: [{v.violation_type.upper()}] {v.property_name}")
        if v.raw_message:
            lines.append(f"  Message: {v.raw_message}")
        if v.trace:
            lines.append(f"  Trace ({len(v.trace)} steps):")
            for step in v.trace:
                lines.append(f"    State {step.step_number}: {step.state_description}")
                for var, val in step.variables.items():
                    lines.append(f"      /\\ {var} = {val}")

    lines.append("\n" + "=" * 60)
    return "\n".join(lines)


def format_result_tsv(
    iteration: int,
    result: TLCResult,
    action: str,
    summary: str = "",
) -> str:
    """Format a single TSV line for results.tsv logging."""
    fields = [
        str(iteration),
        action,
        str(result.violation_count),
        str(result.invariant_violations),
        str(result.deadlocks),
        str(result.liveness_failures),
        str(result.states_found),
        str(result.distinct_states),
        f"{result.time_seconds:.1f}",
        "PASS" if result.passed else "FAIL",
        summary.replace("\t", " "),
    ]
    return "\t".join(fields)


TSV_HEADER = (
    "iteration\taction\tviolations\tinvariant\tdeadlock\tliveness\t"
    "states_found\tdistinct_states\ttime_s\tstatus\tsummary"
)


# -- CLI for direct usage -----------------------------------------------

def main() -> None:
    """Run TLC on a spec and print results. Usage: python prepare.py check <spec.tla>"""
    if len(sys.argv) < 3 or sys.argv[1] != "check":
        print(f"Usage: python {sys.argv[0]} check <spec.tla> [config.cfg] [--timeout N]")
        sys.exit(1)

    spec = sys.argv[2]
    config = None
    timeout = DEFAULT_TIMEOUT

    i = 3
    while i < len(sys.argv):
        if sys.argv[i] == "--timeout" and i + 1 < len(sys.argv):
            timeout = int(sys.argv[i + 1])
            i += 2
        elif not sys.argv[i].startswith("--"):
            config = sys.argv[i]
            i += 1
        else:
            i += 1

    result = run_tlc(spec, config, timeout=timeout)
    print(format_result_for_agent(result))

    quality = evaluate_spec_quality(result, spec)
    print(f"\nSpec Quality: {quality.invariant_count} invariants, "
          f"{quality.temporal_count} temporal props, "
          f"{quality.spec_lines} lines")

    sys.exit(0 if result.passed else 1)


if __name__ == "__main__":
    main()
