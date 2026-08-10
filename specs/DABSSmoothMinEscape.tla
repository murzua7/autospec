---- MODULE DABSSmoothMinEscape ----
\* SMOOTH-1: negative-mass escape through an unclamped smooth_min accumulator.
\*
\* Target: dabs/smooth.py:45 smooth_min(a, b, tau), which is LogSumExp,
\*   -tau * log(exp(-a/tau) + exp(-b/tau)).
\* It UNDERSHOOTS: smooth_min(a,b) <= min(a,b) for all a,b, with the worst
\* case exactly at a = b, where it returns x - tau*ln2.  So two structurally
\* non-negative operands can produce a NEGATIVE result.
\*
\* TLA+ has no reals, so the operator is modelled as its exact counterpart
\* minus a bounded nondeterministic gap, d \in 0..GapMax, with GapMax the
\* integer stand-in for tau*ln2.  That is precisely the guarantee the operator
\* gives, and it is what makes the escape checkable.
\*
\* Two consumers are modelled side by side over one rollout:
\*   stock    -- the accumulator fed by clamp_min(0) applied to the result
\*   stockRaw -- the accumulator fed by the raw result (the live defect shape:
\*               unfloored `expansion` in batched/agents/firms.py and unfloored
\*               `finance_scale` in batched/simulation.py)

EXTENDS Integers

CONSTANTS
    MaxSteps,       \* rollout length
    MaxOperand,     \* bound on the two structurally non-negative operands
    GapMax          \* integer stand-in for tau*ln2

ASSUME /\ MaxSteps \in Nat
       /\ MaxOperand \in Nat
       /\ GapMax \in Nat

VARIABLES
    t,              \* step counter (the rollout clock)
    stock,          \* accumulator fed by the CLAMPED result
    stockRaw,       \* accumulator fed by the UNCLAMPED result
    lastRaw,        \* smooth_min result produced by the most recent step
    escaped         \* TRUE once some step produced a negative result

vars == <<t, stock, stockRaw, lastRaw, escaped>>

Min(a, b) == IF a =< b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* The undershooting operator: exact min, minus a gap of at most tau*ln2.
SmoothMin(a, b, d) == Min(a, b) - d

MaxGain == MaxOperand * MaxSteps
MaxLoss == GapMax * MaxSteps

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t        \in 0..MaxSteps
    /\ stock    \in 0..MaxGain
    /\ stockRaw \in (0 - MaxLoss)..MaxGain
    /\ lastRaw  \in (0 - GapMax)..MaxOperand
    /\ escaped  \in BOOLEAN

\* -- Initial state -------------------------------------------------------
Init ==
    /\ t        = 0
    /\ stock    = 0
    /\ stockRaw = 0
    /\ lastRaw  = 0
    /\ escaped  = FALSE

\* -- Actions -------------------------------------------------------------
\* One step of the rollout: both operands are structurally non-negative, the
\* gap is adversarial within its guaranteed bound, and both accumulators are
\* advanced by the same underlying result.
Step(a, b, d) ==
    /\ t < MaxSteps
    /\ t' = t + 1
    /\ LET r == SmoothMin(a, b, d)
       IN  /\ lastRaw'  = r
           /\ stock'    = stock + Max(r, 0)
           /\ stockRaw' = stockRaw + r
           /\ escaped'  = escaped \/ (r < 0)

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ \E a \in 0..MaxOperand, b \in 0..MaxOperand, d \in 0..GapMax :
           Step(a, b, d)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* What clamp_min(0) buys: an undershooting smooth_min can never drive the
\* accumulator below zero.  Delete the Max(r, 0) from Step -- i.e. model the
\* code as it is written today -- and this fails.
FlooredNonNegative == stock >= 0

\* The undershoot is bounded by ONE tau*ln2 per application.  Fails if a call
\* site applies the operator twice per step, or nests it, without accounting
\* for the compounding gap.
GapBounded == lastRaw >= 0 - GapMax

\* The defect is one-sided and DOWNWARD: the unclamped accumulator may sit
\* below the clamped one but never above it.  A clamp with the wrong sign, or
\* an operator that overshot rather than undershot, breaks this.
NoPhantomGain == stockRaw =< stock

\* Total escaped mass over the rollout is bounded by one gap per application,
\* so the leak is linear in rollout length, not unbounded.
EscapeBounded == stockRaw >= stock - MaxLoss

\* Once an undershoot has driven a step negative, the two paths have provably
\* diverged and never reconverge: the unclamped accumulator stays strictly
\* below the clamped one for the rest of the rollout.
EscapeIsReal == escaped => stockRaw < stock

\* -- Action property -----------------------------------------------------
\* The clamped accumulator is monotone; the economy genuinely evolves while
\* the non-negativity invariant stays pinned.
FlooredMonotone == [][stock' >= stock]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
