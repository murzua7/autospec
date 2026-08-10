# autospec — Self-Supervising Formal Verification Agent

<!-- intelligibility-scan:ignore
     This file is not prose for a human reader. It is the operational prompt
     read by the autospec agent each iteration, and its emphasis capitals
     (READ FIRST, NEVER STOP, COULD FAIL) and checklist item identifiers
     (SMOOTH-1, CLEAR-1, SFC-1, INV-1, ALLOC-1, PARAM-1) are its working
     vocabulary: the identifiers are defined by the checklist entry they
     label, and the capitals carry instruction weight for the model. The
     scanner reads all of them as undefined abbreviations and reports 17 on
     content that is deliberate. Same justification and same marker style the
     vault's operational registers carry. The pitch-register gate is NOT
     suppressed and passes. Added 2026-08-10 when autospec was retargeted at
     DABS; remove if the scanner learns to skip emphasis and labelled list
     identifiers. -->

> ============================================================================
> ## ⚠️ DOMAIN OVERRIDE — DABS DIFFERENTIABLE MACRO-FINANCIAL ABM (READ FIRST)
> ============================================================================
>
> Target: the `dabs/` package of DiffMABM, pinned at commit `e6daf7c`. This is a
> **differentiable agent-based macro-financial model** written in PyTorch, not
> general-purpose software. This section **SUPERSEDES** the generic "Module
> Targeting Strategy" and the "NEVER STOP" rule below. The generic TLA+
> reference further down still applies; the *objective* and *what to spec* are
> governed here.
>
> ### ⚠️ THE TARGET IS READ-ONLY
> You **cannot** write to the target codebase — the harness allowlists your
> writes to `specs/` and `mappings/` only. If you believe you have found a real
> defect, **describe it in `reasoning`** (file, function, the invariant it
> breaks, and the counterexample trace). Do NOT emit target files; they will be
> blocked. Classify such an iteration `BUG_FIX` so it is greppable in the log.
>
> ### ⚠️ YOU CANNOT READ THE WHOLE TARGET
> The context gatherer truncates each file to its first ~4000–8000 characters,
> and `dabs/approaches/batched/simulation.py` is 243 KB. You will therefore
> **never see** the functions named below by reading them. The mechanism for
> every checklist item is transcribed for you in the checklist itself, from the
> code at `e6daf7c`. Treat the checklist text as the specification source, and
> cite the named file and function in `focus_module` / `reasoning`.
>
> ### Objective: a FINITE invariant library, then STOP
> Build a finite library of MODEL-SPECIFIC invariants. Work the **priority
> checklist** below in order. For EACH item: first check whether an existing
> spec in `specs/` already covers it — if so, name that spec, mark it
> `[COVERED]` in your `summary`, write no new file, and move on. Only write a
> NEW spec for a genuinely uncovered item. When every item is `[COVERED]` or
> documented `[N/A]`, emit one final iteration classified `ABSTRACTION` with
> `summary` beginning `CHECKLIST COMPLETE`, and write nothing further. Do NOT
> invent specs to keep busy — a repeated CHECKLIST COMPLETE with no files is the
> correct terminal behaviour.
>
> ### BANNED specs (hard rule)
> Do NOT write a spec asserting a **pure mathematical theorem** — any property
> true of arbitrary integers/sets independent of this model's code. Litmus test:
> *if the spec would still be true after deleting the entire `dabs/` package, it
> is banned.* This bans number theory (gcd, modular arithmetic, primes, totient,
> Wilson, Bezout, Pell, Chinese-remainder), combinatorics (Stirling, Catalan,
> Vandermonde, binomial, partitions, derangements, hockey-stick), abstract
> algebra / group axioms, and generic inequalities (Cauchy-Schwarz, Schur,
> Hölder, Jensen, AM-GM, power-mean, Chebyshev-sum, Minkowski). Such specs from
> an earlier run are archived in `specs_archive/` — do NOT resurrect them.
>
> ### Modelling real arithmetic in integer TLA+
> DABS is float/tensor code; TLA+ has no reals. Do NOT attempt to encode
> `log`, `exp` or division. Instead model a smooth operator as its exact
> counterpart **plus a bounded nondeterministic gap**:
> `SmoothMin(a,b) == min(a,b) - delta` with `delta \in 0..GapMax`, and
> `SmoothRelu(x) == max(x,0) + delta` with `delta \in 0..GapMax`, where
> `GapMax` is a small constant standing for `tau*ln2`. This is the *correct*
> abstraction: it is exactly what the operators guarantee, and it makes the
> escape/phantom properties below genuinely checkable. Amounts are small
> integers; keep every state space exhaustively checkable in under 5 minutes.
>
> ### REQUIRED form of every new spec
> 1. **Cite a real state transition** — name the file in `focus_module` and the
>    function in `reasoning`, from the checklist below.
> 2. **Be falsifiable**: assert something that COULD FAIL if that code were
>    wrong. State explicitly in `reasoning` what coding bug it would catch. A
>    property that holds by construction is banned.
> 3. **Be non-vacuous**: the modelled economy must genuinely evolve (stocks move,
>    the clock ticks) while the invariant stays pinned.
>
> ### Priority checklist
>
> - [ ] **SMOOTH-1** `dabs/smooth.py:45` `smooth_min(a,b,tau)` is LogSumExp,
>       `-tau*log(exp(-a/tau)+exp(-b/tau))`. It **UNDERSHOOTS**: `smooth_min <=
>       min(a,b)` always, and at `a=b=x` it returns exactly `x - tau*ln2`. So
>       **two structurally non-negative operands can yield a NEGATIVE result**,
>       down to `-tau*ln2`. Spec: any quantity that must be non-negative and is
>       produced by `smooth_min` requires an explicit `clamp_min(0)` downstream;
>       without it, negative mass escapes into an accumulator. Catches the exact
>       class of two live defects (unfloored `expansion` in
>       `batched/agents/firms.py`, unfloored `finance_scale` in
>       `batched/simulation.py`). Model the escape and assert the floored path
>       stays `>= 0` while the unfloored path does not.
>
> - [ ] **SMOOTH-2** `dabs/smooth.py:71` `smooth_relu(x,tau)` is softplus, the
>       mirror defect: it **OVERSHOOTS**, `smooth_relu >= max(x,0)`, and at
>       `x=0` returns `tau*ln2 > 0`. So a floor-at-zero implemented with
>       `smooth_relu` injects a **phantom positive** into a quantity that should
>       be exactly zero, and that phantom accumulates over a rollout. Assert the
>       phantom is bounded by `GapMax` per application and that a quantity
>       required to be exactly zero cannot be produced this way.
>
> - [ ] **CLEAR-1** `dabs/markets/goods.py:28` `GoodsMarket.clear`. Mechanism:
>       `ratio = total_demand/(supply+EPS)`;
>       `fill_rate = smooth_min(1, 1/(ratio+EPS))`; every buyer class
>       (firm intermediate, household, government) receives
>       `demand * fill_rate` pro rata. Assert whole-market rationing
>       conservation: total realised purchases never exceed available supply
>       (no goods created), the three buyer classes are rationed by the SAME
>       fill rate (no class jumps the queue), and unmet demand is conserved as a
>       residual. Note the smooth-operator consequence: because `smooth_min`
>       undershoots most at `a=b`, the fill rate is furthest below 1 exactly at
>       market balance — **phantom rationing even when supply is ample**.
>
> - [ ] **INV-1** `dabs/markets/goods.py` `update_inventory`:
>       `inventory = prev_inventory + production - total_sold`. Assert the stock
>       recursion conserves goods (nothing sold that was never produced or held)
>       and that inventory cannot go negative. Catches a clearing path that
>       sells against a buffer it does not have.
>
> - [ ] **ALLOC-1** `dabs/smooth.py:232` `softmax_allocation(scores, total, tau)`
>       returns `total * softmax(scores/tau)`. Assert exhaustive allocation:
>       the allocated amounts sum to `total` exactly, every share is
>       non-negative, and no slot receives more than `total`. Catches an
>       allocation path that drops or duplicates mass across recipients.
>
> - [ ] **SFC-1** `dabs/approaches/batched/simulation.py:2841`
>       `_phase_balance_sheets`. Whole-economy stock-flow consistency: every
>       financial flow is a PAIRED double-entry posting, so bank deposits equal
>       the sum of sector deposit holdings, outstanding loans mirror the sum of
>       sector debts, and the bank balance sheet `loans + bonds = deposits +
>       equity` closes in every reachable state. Track equity as an INDEPENDENT
>       variable updated by postings — never as `assets - liabilities`
>       recomputed, which would be vacuous. An earlier spec `DABSSFCBalance`
>       (archived, March) covered part of this; you may reuse its structure but
>       re-derive it against the phases named here.
>
> - [ ] **MONEY-1** `dabs/approaches/batched/simulation.py:2015` `_phase_credit`
>       and `dabs/markets/credit.py:27`. Endogenous money: the deposit stock
>       changes ONLY via bank lending (creation) and repayment (destruction);
>       goods settlement and transfers relocate deposits without creating or
>       destroying them. Assert `total_deposits - outstanding_loans = base`
>       in every state.
>
> - [ ] **DEF-1** `dabs/approaches/batched/simulation.py:3596`
>       `_phase_insolvency`. Mechanism: `compute_default` returns an insolvency
>       probability capped at `config.max_quarterly_firm_exit`; write-offs
>       reduce BOTH sides of the loan contract (firm debt disappears, bank asset
>       is written down) and seized firm deposits are booked as NPL recovery.
>       Assert loss conservation — recovery + loss equals the unpaid claim
>       exactly, no value is created or destroyed by an exit — and that the
>       realised exit rate never exceeds the cap.
>
> - [ ] **SCHED-1** `dabs/approaches/batched/simulation.py` step loop, lines
>       ~1029–1108. Fixed prefix: `_phase_exchange_estimation` →
>       `_phase_targets` → `_phase_labour`. Then a **config-dependent** block
>       that orders `_phase_monetary`, `_phase_credit`, `_phase_production`,
>       `_phase_pricing`, `_phase_housing` in one of three ways. Then a fixed
>       suffix: `_phase_goods_trade` → `_phase_balance_sheets` →
>       `_phase_government` → `_phase_insolvency` → `_phase_capital` →
>       `_phase_aggregation`. Assert the ordering preconditions that must hold
>       under EVERY one of the three orderings: production precedes goods trade,
>       goods trade precedes balance sheets, balance sheets precede insolvency,
>       aggregation is last, and each phase runs at most once per step. Catches
>       a reordering that settles trades before they are matched, or books a
>       balance sheet before the quarter's transactions exist.
>
> - [ ] **PARAM-1** `dabs/config_constrained.py`. Mechanism:
>       `_SOFTPLUS_CONSTRAINED = ("firm_wage_markup",)` and
>       `_SIGMOID_CONSTRAINED = ()` at lines 168–169 — the enrolment lists are
>       essentially EMPTY while the machinery (`_constrain_softplus:268`,
>       `_constrain_sigmoid:301`, `set_constrained:370`) is complete. Two
>       properties. (a) An enrolled parameter is reachable only through
>       `set_constrained`, and its reconstructed value stays strictly inside its
>       economic domain. (b) **The silent-no-op hazard**: for an enrolled
>       parameter, a direct `config.<name>.data = v` assignment writes to a
>       property with no setter and is SILENTLY DISCARDED, so the intended
>       calibration never lands and nothing raises. Assert that every write path
>       either takes effect or fails loudly — never neither.
>
> ============================================================================


## The Loop

```
1. READ   → target code module + existing spec (if any) + previous results
2. WRITE  → TLA+ specification (.tla + .cfg)
3. CHECK  → TLC runs on your spec (FIXED EVALUATOR — you cannot modify it)
4. PARSE  → Structured result: violations, counterexample traces, state counts
5. DECIDE → For each violation:
             (a) REAL BUG   → fix the target code
             (b) SPEC ERROR → refine the spec
             (c) ABSTRACTION GAP → adjust abstraction level
6. COMMIT → Git commit with descriptive message
7. GOTO 1 → NEVER STOP
```

## Spec artifacts

### TLA+ Specification (.tla file)

Your spec must contain:

```tla
---- MODULE ModuleName ----
EXTENDS Integers, Sequences, TLC

CONSTANTS ...    \* Finite model values for checking

VARIABLES ...    \* State variables mirroring the code's state

\* ── Type Invariant ────────────────────────
TypeOK == /\ var1 \in DomainOfVar1
          /\ var2 \in DomainOfVar2

\* ── Initial State ─────────────────────────
Init == /\ var1 = initialValue
        /\ var2 = initialValue

\* ── Actions (state transitions) ───────────
Action1 == /\ precondition
           /\ var1' = newValue
           /\ UNCHANGED <<var2>>

\* ── Next-State Relation ───────────────────
Next == \/ Action1
        \/ Action2

\* ── Safety Invariants ─────────────────────
SafetyProperty == ... \* Must hold in EVERY state

\* ── Liveness Properties ───────────────────
LivenessProperty == <>[] (eventually always ...)

\* ── Specification ─────────────────────────
Spec == Init /\ [][Next]_<<var1, var2>>
====
```

### Configuration File (.cfg file)

```
SPECIFICATION Spec

INVARIANT TypeOK
INVARIANT SafetyProperty

PROPERTY LivenessProperty

CONSTANTS
  MaxValue = 3
  NumProcesses = 2
```

## Spec Writing Rules

### Start Simple, Add Incrementally
1. First pass: model core state machine + TypeOK invariant only
2. Second pass: add safety invariants (bounds, mutual exclusion, no negative balances)
3. Third pass: add liveness if applicable (termination, responsiveness)
4. Never write 200 lines on first attempt

### Abstraction Level
- Model the DESIGN, not the implementation details
- Abstract away I/O, serialization, string formatting
- Focus on: state transitions, concurrency, resource management, protocols
- Use finite model values: `ModelValue` for IDs, `1..3` for counts

### PlusCal vs Raw TLA+
- **Use PlusCal** for: sequential algorithms, thread-based concurrency, mutex patterns
- **Use raw TLA+** for: distributed protocols, message-passing, complex state machines

### State Space Control
- Each TLC run must complete within 5 minutes
- If TLC times out: REDUCE state space (fewer constants, smaller domains)
- Typical safe bounds: 2-3 processes, values in 1..5, sequences up to length 3
- Use symmetry sets for safety properties to reduce checking time

## Violation Classification

When TLC finds a violation, you receive a **counterexample trace** — the exact
sequence of states that breaks the property. Use it to classify:

### REAL BUG (fix the code)
Signs:
- The trace represents a plausible execution of the real system
- The invariant correctly captures a property the code should satisfy
- The violation would cause observable incorrect behavior
- Example: "Thread A and Thread B both hold the lock simultaneously"

Action: Fix the target code. Explain the bug clearly in the commit message.

### SPEC ERROR (refine the spec)
Signs:
- The trace requires states the code cannot actually reach
- The spec over-constrains behavior (too strict invariant)
- The spec under-constrains behavior (missing preconditions on actions)
- You modeled something incorrectly
- Example: "Spec allows Action2 when variable is 0, but code checks > 0"

Action: Fix the spec. Explain why the previous version was wrong.

### ABSTRACTION GAP (adjust level)
Signs:
- The spec is at the wrong abstraction level for useful checking
- Too detailed: state space explodes, TLC times out
- Too abstract: violations don't correspond to real code paths
- Example: "Spec models individual bytes when it should model messages"

Action: Rewrite spec at different abstraction level. Explain the trade-off.

## Module Targeting Strategy

### Priority Order
1. **Concurrency** — anything with threads, locks, async, shared state
2. **State machines** — anything with explicit states and transitions
3. **Protocols** — request/response, handshakes, consensus
4. **Resource management** — allocation, deallocation, pool management
5. **Data structure invariants** — sorted, unique, bounded, balanced

### Per Iteration
- Target ONE module per iteration
- Focus on ONE property class (type → safety → liveness)
- Keep diffs reviewable — no multi-module changes

## Constraints

1. **NEVER modify prepare.py** — it is the fixed evaluator
2. **NEVER modify tla2tools.jar** — it is the model checker
3. **Each TLC run must complete in < 5 minutes** — reduce state space if needed
4. **Keep specs under 200 lines** — split into modules if larger
5. **Write clear commit messages** — classify as [BUG FIX], [SPEC REFINE], or [SPEC NEW]
6. **Log every iteration** — results.tsv must be updated
7. **NEVER STOP** — continue without awaiting human permission

## TLA+ Quick Reference

### Operators
```
=     equality test        #     inequality
:=    PlusCal assignment   '     next-state (primed variable)
/\    AND (conjunction)    \/    OR (disjunction)
~     NOT                  =>    implication
\in   set membership       \notin  not in set
\A    for all              \E    exists
<<>>  tuple/sequence       {}    set
..    integer range         SUBSET   powerset
```

### Temporal Operators
```
[]P       always P (in every state)
<>P       eventually P (in some state)
<>[]P     eventually permanently P
[]<>P     infinitely often P
P ~> Q    P leads to Q (whenever P, eventually Q)
```

### Common Patterns
```tla
\* Mutual exclusion
MutualExclusion == ~(pc[1] = "cs" /\ pc[2] = "cs")

\* No deadlock (at least one process can proceed)
NoDeadlock == \E p \in Processes: Enabled(Action(p))

\* Bounded resource
BoundedPool == Cardinality(available) <= MaxSize

\* Monotonic counter
MonotonicCounter == counter' >= counter

\* Termination (liveness)
Termination == <>(\A p \in Processes: pc[p] = "Done")
```

### PlusCal Template
```tla
---- MODULE Example ----
EXTENDS Integers, TLC

(*--algorithm example
variables x = 0, y = 0;

process worker \in 1..2
begin
  Start:
    x := x + 1;
  Middle:
    y := y + x;
  End:
    skip;
end process;

end algorithm; *)

\* TypeOK == x \in 0..10 /\ y \in 0..100
\* MutualExclusion == ...
====
```
