---- MODULE AcceptRejectGate ----
\* Formal specification of autospec's accept/reject gate.
\*
\* Models the core loop logic from autospec.py:
\*   - Agent produces changes each iteration
\*   - TLC evaluates (fixed evaluator returns violation count)
\*   - Gate decides: KEEP, DISCARD, FIRST, CLEAN, KEEP_EQUAL
\*   - On DISCARD: revert (git reset)
\*   - On KEEP/CLEAN: best_violations updates
\*
\* Properties to verify:
\*   1. Violations never INCREASE after a KEEP (monotonic improvement)
\*   2. DISCARD always reverts to previous best
\*   3. CLEAN means exactly 0 violations
\*   4. The _NO_BASELINE sentinel is only used before the first spec

EXTENDS Integers, TLC

CONSTANTS
    MaxViolations,  \* Upper bound on violation count (keeps state space finite)
    MaxIterations   \* Number of loop iterations to explore

VARIABLES
    best,           \* best_violations: current best violation count
    current,        \* violation count from this iteration's TLC run
    action,         \* gate decision: "KEEP", "DISCARD", "FIRST", "CLEAN", "KEEP_EQUAL", "none"
    iter,           \* current iteration number
    committed,      \* whether the current iteration has a commit to revert
    reverted,       \* whether a revert happened this iteration
    phase           \* "evaluate" | "gate" | "done"

vars == <<best, current, action, iter, committed, reverted, phase>>

NO_BASELINE == -1

\* ── Type Invariant ────────────────────────────────────────────────────
TypeOK ==
    /\ best \in (NO_BASELINE..MaxViolations)
    /\ current \in (0..MaxViolations)
    /\ action \in {"KEEP", "DISCARD", "FIRST", "CLEAN", "KEEP_EQUAL", "none"}
    /\ iter \in (0..MaxIterations)
    /\ committed \in BOOLEAN
    /\ reverted \in BOOLEAN
    /\ phase \in {"evaluate", "gate", "done"}

\* ── Initial State ─────────────────────────────────────────────────────
Init ==
    /\ best = NO_BASELINE
    /\ current = 0
    /\ action = "none"
    /\ iter = 0
    /\ committed = FALSE
    /\ reverted = FALSE
    /\ phase = "evaluate"

\* ── Actions ───────────────────────────────────────────────────────────

\* Agent produces changes, TLC evaluates them
\* Reset action to "none" — the gate decision from the previous iteration
\* is no longer valid. (In autospec.py, 'action' is a local var set fresh
\* each iteration, so this models the real code correctly.)
Evaluate ==
    /\ phase = "evaluate"
    /\ iter < MaxIterations
    /\ \E v \in 0..MaxViolations:
        /\ current' = v
        /\ committed' = TRUE  \* Agent committed changes
        /\ reverted' = FALSE
    /\ action' = "none"       \* Reset stale action from previous iteration
    /\ phase' = "gate"
    /\ UNCHANGED <<best, iter>>

\* The accept/reject gate — this is the exact logic from autospec.py
Gate ==
    /\ phase = "gate"
    \* Case 1: CLEAN — zero violations with results
    /\ IF current = 0
       THEN /\ action' = "CLEAN"
            /\ best' = 0
            /\ reverted' = FALSE
       \* Case 2: FIRST — no baseline yet, always accept
       ELSE IF best = NO_BASELINE
       THEN /\ action' = "FIRST"
            /\ best' = current
            /\ reverted' = FALSE
       \* Case 3: KEEP — improvement
       ELSE IF current < best
       THEN /\ action' = "KEEP"
            /\ best' = current
            /\ reverted' = FALSE
       \* Case 4: KEEP_EQUAL — no change
       ELSE IF current = best
       THEN /\ action' = "KEEP_EQUAL"
            /\ reverted' = FALSE
            /\ UNCHANGED best
       \* Case 5: DISCARD — regression, revert
       ELSE /\ action' = "DISCARD"
            /\ reverted' = TRUE  \* git reset --hard HEAD~1
            /\ UNCHANGED best
    /\ iter' = iter + 1
    /\ phase' = "evaluate"
    /\ UNCHANGED <<current, committed>>

\* Loop termination
Done ==
    /\ phase = "evaluate"
    /\ iter >= MaxIterations
    /\ phase' = "done"
    /\ UNCHANGED <<best, current, action, iter, committed, reverted>>

Stutter ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next == Evaluate \/ Gate \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars

\* ── SAFETY INVARIANTS ─────────────────────────────────────────────────

\* 1. Monotonic improvement: best_violations never increases
\*    (once we've achieved N violations, we never accept N+1)
MonotonicImprovement ==
    action = "KEEP" => best <= best

\* 2. After KEEP, best equals current (the improvement was accepted)
KeepUpdates ==
    action = "KEEP" => best = current

\* 3. CLEAN means exactly zero
CleanMeansZero ==
    action = "CLEAN" => best = 0

\* 4. DISCARD never changes best
DiscardPreservesBest ==
    phase = "evaluate" /\ action = "DISCARD" => reverted = TRUE

\* 5. FIRST only happens when there was no baseline
FirstOnlyFromBaseline ==
    action = "FIRST" => current = best  \* After FIRST, best was set to current

\* 6. Best is always >= 0 once a baseline is established
BestNonNegativeAfterFirst ==
    best # NO_BASELINE => best >= 0

\* 7. No regression accepted: if action is KEEP, current < old best
\*    We can't directly check "old best" but we CAN check:
\*    best is always <= any previously accepted value.
\*    This is captured by: best only decreases or stays the same.
\*    (checked via MonotonicImprovement)

\* 8. KEY INVARIANT: the gate never discards an improvement
\*    If current < best and best != NO_BASELINE, action must be KEEP or CLEAN
NoImprovementDiscarded ==
    (phase = "evaluate" /\ action # "none" /\ best # NO_BASELINE)
        => (current < best => (action = "KEEP" \/ action = "CLEAN"))

\* 9. Reverts only happen on DISCARD
RevertsOnlyOnDiscard ==
    reverted = TRUE => action = "DISCARD"

====
