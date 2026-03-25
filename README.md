<p align="center">
  <img src="https://img.shields.io/badge/TLA%2B-Model%20Checked-blue?style=for-the-badge" />
  <img src="https://img.shields.io/badge/Python-3.10%2B-green?style=for-the-badge&logo=python&logoColor=white" />
  <img src="https://img.shields.io/badge/Claude-Anthropic-orange?style=for-the-badge" />
  <img src="https://img.shields.io/badge/Tests-29%20passed-brightgreen?style=for-the-badge" />
</p>

# autospec

**A self-supervising formal verification loop that uses an LLM agent + the TLC model checker to find bugs no test suite ever will.**

Inspired by [Karpathy's autoresearch](https://github.com/karpathy/autoresearch) — but instead of optimizing training loss, we're eliminating bugs. The model checker is the fixed evaluator: mathematically exhaustive, deterministic, and impossible to game.

---

## The Problem

Tests check the cases you think of. Formal verification checks **every** case.

AWS found a bug in a distributed protocol that required a [35-step error trace](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/) — a sequence so specific that no human would write a test for it, and no fuzzer would find it in a reasonable time. TLA+ and its model checker TLC found it by exploring **every reachable state**.

The barrier? Writing TLA+ specifications is hard. It requires translating code into a formal state machine, defining invariants, and iterating when the spec is wrong.

**autospec automates this entire process.**

## How It Works

An LLM agent sits in a tight loop with the TLC model checker — the same tool AWS uses to verify S3, DynamoDB, and EBS:

```
         ┌─────────────────────────────────────────────┐
         │              program.md                      │
         │        (strategy — human-curated)            │
         └──────────────────┬──────────────────────────┘
                            │
    ┌───────────────────────▼───────────────────────────┐
    │                                                    │
    │   1. READ   target code                            │
    │   2. WRITE  TLA+ spec (.tla + .cfg)                │
    │   3. CHECK  run TLC model checker  ◄── IMMUTABLE   │
    │   4. PARSE  violations + counterexample traces     │
    │   5. DECIDE                                        │
    │      ├── Real bug?  → fix the code                 │
    │      ├── Spec error? → refine the spec             │
    │      └── Abstraction gap? → adjust level           │
    │   6. COMMIT  git (keep if improved, revert if not) │
    │   7. GOTO 1  ── NEVER STOP                         │
    │                                                    │
    └────────────────────────────────────────────────────┘
```

### The Autoresearch Analogy

| [autoresearch](https://github.com/karpathy/autoresearch) | autospec | Why it matters |
|---|---|---|
| `train.py` (mutable genome) | TLA+ specs + target code | Agent iterates on both |
| `prepare.py` (fixed evaluator) | `prepare.py` (TLC harness) | SHA256-verified each iteration |
| `val_bpb` (scalar fitness) | Violation count + **counterexample traces** | Structured feedback >> scalar |
| `program.md` (strategy) | `program.md` (strategy) | Encode verification intuition |
| `git reset` on regression | `git reset --hard HEAD~1` | Only improvements survive |
| 5-min training budget | 5-min TLC timeout | Bounded evaluation window |

**But autospec is strictly stronger** — TLC is a *complete* evaluator. It explores every reachable state, not a sample. A training loss can be gamed; an exhaustive model checker cannot.

## Quick Start

```bash
# Clone
git clone https://github.com/murzua7/autospec.git
cd autospec

# Install
pip install -e .

# TLC downloads automatically on first run (requires Java 11+)
java -version

# Run TLC on the example spec (no API key needed)
python -m autospec --check specs/BankTransfer.tla

# Run the full loop (queue mode — no API key needed, works with Claude Code Max)
python -m autospec --target /path/to/your/code --max-iters 100

# Or with direct API mode (requires credits)
python -m autospec --target /path/to/your/code --mode api
```

### Agent Modes

| Mode | Flag | Requires | How it works |
|------|------|----------|-------------|
| **Queue** (default) | `--mode queue` | A separate LLM process (e.g. Claude Code) | Writes prompts to `llm_queue/requests/`, polls for responses in `llm_queue/responses/` |
| **API** | `--mode api` | `ANTHROPIC_API_KEY` with credits | Direct Anthropic API call each iteration |

Queue mode is the default because it works with Claude Code Max subscriptions (no API credits needed). A separate Claude Code session or any LLM process reads the queue and writes responses.

## What TLC Finds (That Tests Can't)

### Example: Bank Transfer Race Condition

The included example (`target/example/bank_transfer.py`) has a deliberate TOCTOU bug in a concurrent bank transfer:

```python
def transfer(self, from_id, to_id, amount):
    current_balance = from_acc.balance      # READ  (non-atomic)
    if current_balance < amount:            # CHECK (stale value!)
        return False
    from_acc.balance = current_balance - amount  # WRITE (stale!)
    to_acc.balance += amount
```

You could run the threaded version 10,000 times and maybe see the bug once. **TLC finds it in <2 seconds by exploring all 2,836 reachable states:**

```
============================================================
TLC RESULT: BankTransfer.tla
============================================================
Passed: NO
Violations: 1 (Invariant: MoneyConserved)

VIOLATION 1: [INVARIANT] MoneyConserved
  Trace (5 steps):
    State 1: balance = (a1:0, a2:1), init_total = 1
    State 2: t1 starts transfer from a2→a1
    State 3: t1 reads balance[a2] = 1          ← snapshot
    State 4: t1 checks: 1 >= 1, proceeds
    State 5: t1 writes balance[a2] = 1-1 = 0   ← but total is now 0 ≠ 1
============================================================
```

The counterexample trace tells the agent *exactly* what went wrong — not just "it failed," but the precise 5-step sequence of states that violates money conservation.

## Self-Verification: autospec Verified Itself

We ran autospec on its own codebase. TLC verified 3 critical subsystems across **5,423 states** and **22 invariants**:

| Spec | States | Invariants | What it proved |
|------|--------|-----------|---------------|
| `AcceptRejectGate.tla` | 244 | 8 | Loop never accepts a regression; reverts only on DISCARD; CLEAN = zero violations |
| `FileSandbox.tla` | 2,304 | 7 | Forbidden files never written; path traversal blocked; only allowed dirs writable |
| `IntegrityCheck.tla` | 39 | 4 | Evaluator integrity verified before every trust boundary |

### Bugs Found in autospec by autospec

**1. Defense-in-depth gap** (IntegrityCheck.tla, 10-step trace)

TLC found that the integrity check could be skipped between `apply_changes()` and `evaluate_all_specs()`. Under adversarial conditions, a compromised evaluator could run for one iteration before detection.

*Fixed:* Added second integrity check right before the evaluation trust boundary.

**2. Stale state between iterations** (AcceptRejectGate.tla)

TLC showed the gate decision variable persisted across iteration boundaries — a state machine hygiene issue that could mask bugs in future changes.

*Fixed:* Explicit state reset in the Evaluate action.

## Architecture

```
autospec/
├── prepare.py          # IMMUTABLE evaluator (TLC harness + parser)
│                       #   SHA256 integrity-checked every iteration
├── autospec.py         # Main loop orchestrator (agent + git + accept/reject)
├── program.md          # Agent strategy document (TLA+ guidelines + heuristics)
├── __main__.py         # CLI entry point
├── specs/              # TLA+ specifications (agent-mutable)
│   ├── AcceptRejectGate.tla/.cfg  # Self-spec: loop logic
│   ├── FileSandbox.tla/.cfg       # Self-spec: security sandbox
│   ├── IntegrityCheck.tla/.cfg    # Self-spec: evaluator integrity
│   └── BankTransfer.tla/.cfg      # Example: concurrent race condition
├── target/             # Target codebase (agent-mutable for fixes)
├── mappings/           # Code ↔ Spec correspondence (auto-cleaned on target change)
├── traces/             # Saved counterexample traces
├── llm_queue/          # File-based agent queue (queue mode)
│   ├── requests/       #   Loop writes prompts here
│   └── responses/      #   External LLM writes responses here
├── tests/              # Unit + integration + security tests
└── lib/                # tla2tools.jar (auto-downloaded)
```

### Target Change Detection

When you point autospec at a new target, it detects the change by comparing the module mapping against the new codebase. If there's no overlap, it automatically cleans stale specs, traces, results, and queue files so old violations don't pollute the new run.

### Agent Capabilities

The agent can:
- **Write** specs and code fixes via the `"files"` dict
- **Delete** obsolete specs via `"delete_specs": ["OldSpec.tla"]` (removes `.tla`, `.cfg`, and trace files)
- **Classify** actions as `NEW_SPEC`, `SPEC_REFINE`, `BUG_FIX`, or `ABSTRACTION`

### Security Model (3 Layers)

The agent runs autonomously — it must be sandboxed:

1. **File sandbox** — `resolve()` + `is_relative_to()` prevents path traversal; directory allowlist restricts writes to `specs/`, `mappings/`, `target/`; forbidden filename set blocks `prepare.py`, `autospec.py`, etc.
2. **Evaluator integrity** — SHA256 hash of `prepare.py` recorded at startup, verified before every TLC run. If hash changes → abort + revert.
3. **Anti-reward-hacking** — Trivial specs (no invariants, 0 states explored) are penalized. TLC itself is deterministic and complete — it cannot be gamed.

All three layers are **formally verified** by TLC (see `specs/FileSandbox.tla` and `specs/IntegrityCheck.tla`).

## What autospec Can Verify

| Category | Examples | What TLC catches |
|----------|---------|-------------------|
| **Concurrency** | Thread pools, locks, async | Race conditions, deadlocks, starvation |
| **State machines** | Workflows, protocols, FSMs | Unreachable states, missing transitions, invariant violations |
| **Resource management** | Connection pools, memory | Leaks, double-free, exhaustion |
| **Distributed systems** | Consensus, replication | Split-brain, message reordering, byzantine failures |
| **Financial logic** | Transfers, ledgers | Conservation violations, negative balances, phantom money |

## Configuration

```bash
# Basic usage (queue mode, no API key needed)
python -m autospec --target ./my-project

# Full options
python -m autospec \
  --target ./my-project \            # Codebase to verify
  --mode api \                       # Use direct API (default: queue)
  --model claude-opus-4-20250514 \   # LLM model (api mode only)
  --max-iters 500 \                  # Maximum loop iterations
  --tag overnight-run                # Git branch tag

# Direct TLC check (no agent, no API key needed)
python -m autospec --check specs/MySpec.tla
```

## Requirements

- Python 3.10+
- Java 11+ (for TLC model checker — `tla2tools.jar` auto-downloads)
- Git
- For **queue mode** (default): an external LLM process (e.g. Claude Code)
- For **api mode**: `anthropic` Python package + `ANTHROPIC_API_KEY`

### Windows

autospec works on Windows (Git Bash / MSYS2). MSYS-style paths (`/c/Users/...`) are automatically normalized to native Windows paths.

## How It Compares

| Tool | Approach | Completeness | Feedback |
|------|----------|-------------|----------|
| **Unit tests** | Check specific cases | Incomplete — you write the cases | Pass/fail |
| **Fuzzing** | Random inputs | Probabilistic — may miss edge cases | Crash/no crash |
| **Property testing** | Random + shrinking | Better but still sampling | Minimal counterexample |
| **Static analysis** | Pattern matching | Fast but shallow | Warnings |
| **autospec** | Exhaustive state exploration | **Complete** for finite models | Exact counterexample trace |

## Acknowledgments

- [Leslie Lamport](https://lamport.azurewebsites.net/) — TLA+ and the temporal logic of actions
- [Andrej Karpathy](https://github.com/karpathy/autoresearch) — The autoresearch loop architecture
- [AWS Formal Methods team](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/) — Proving TLA+ works at scale
- [Learn TLA+](https://learntla.com/) — The best TLA+ tutorial

## License

Apache 2.0
