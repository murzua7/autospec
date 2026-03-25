---- MODULE AcceptRejectGate ----
EXTENDS Naturals

CONSTANTS MaxViolations, MaxIterations

VARIABLES best, current, iter, act, has_baseline
vars == <<best, current, iter, act, has_baseline>>

TypeOK ==
    /\ best \in 0..MaxViolations
    /\ current \in 0..MaxViolations
    /\ iter \in 0..MaxIterations
    /\ act \in {"NONE", "FIRST", "KEEP", "KEEP_EQUAL", "DISCARD", "CLEAN"}
    /\ has_baseline \in BOOLEAN

DiscardMeansRegression ==
    act = "DISCARD" => (has_baseline /\ current > best)

KeepMeansImprovement ==
    act = "KEEP" => (has_baseline /\ current = best)

CleanMeansZero ==
    act = "CLEAN" => current = 0

Init ==
    /\ best = 0 /\ current = 0 /\ iter = 0
    /\ act = "NONE" /\ has_baseline = FALSE

FirstRun(v) ==
    /\ iter < MaxIterations /\ ~has_baseline
    /\ current' = v /\ best' = v /\ act' = "FIRST"
    /\ iter' = iter + 1 /\ has_baseline' = TRUE

CleanRun ==
    /\ iter < MaxIterations /\ has_baseline
    /\ current' = 0 /\ best' = 0 /\ act' = "CLEAN"
    /\ iter' = iter + 1 /\ UNCHANGED has_baseline

KeepRun(v) ==
    /\ iter < MaxIterations /\ has_baseline
    /\ v > 0 /\ v < best
    /\ current' = v /\ best' = v /\ act' = "KEEP"
    /\ iter' = iter + 1 /\ UNCHANGED has_baseline

KeepEqualRun(v) ==
    /\ iter < MaxIterations /\ has_baseline /\ v = best
    /\ current' = v /\ best' = best /\ act' = "KEEP_EQUAL"
    /\ iter' = iter + 1 /\ UNCHANGED has_baseline

DiscardRun(v) ==
    /\ iter < MaxIterations /\ has_baseline /\ v > best
    /\ current' = v /\ best' = best /\ act' = "DISCARD"
    /\ iter' = iter + 1 /\ UNCHANGED has_baseline

Done == /\ iter = MaxIterations /\ UNCHANGED vars

Next ==
    \/ \E v \in 0..MaxViolations: FirstRun(v)
    \/ CleanRun
    \/ \E v \in 1..MaxViolations: KeepRun(v)
    \/ \E v \in 0..MaxViolations: KeepEqualRun(v)
    \/ \E v \in 0..MaxViolations: DiscardRun(v)
    \/ Done

Spec == Init /\ [][Next]_vars
====
