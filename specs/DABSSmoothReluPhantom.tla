---- MODULE DABSSmoothReluPhantom ----
\* SMOOTH-2: phantom positive mass injected by an overshooting smooth_relu.
\*
\* Target: dabs/smooth.py:71 smooth_relu(x, tau), which is softplus,
\*   tau * log(1 + exp(x/tau)).
\* It OVERSHOOTS: smooth_relu(x) >= max(x, 0) for all x, with the worst case
\* exactly at x = 0, where it returns tau*ln2 > 0.  So a floor-at-zero
\* implemented with smooth_relu injects a strictly positive PHANTOM into a
\* quantity that the exact floor would set to exactly zero, and the phantom
\* accumulates over a rollout.  This is the exact mirror of the SMOOTH-1
\* undershoot already covered by DABSSmoothMinEscape.
\*
\* TLA+ has no reals, so the operator is modelled as its exact counterpart
\* PLUS a bounded nondeterministic gap, d \in 0..GapMax, with GapMax the
\* integer stand-in for tau*ln2.  That is precisely the guarantee softplus
\* gives, and it is what makes the phantom checkable.
\*
\* Two consumers are modelled side by side over one rollout:
\*   hardStock -- the accumulator fed by max(x, 0), the exact floor
\*   softStock -- the accumulator fed by smooth_relu, the defect shape

EXTENDS Integers

CONSTANTS
    MaxSteps,       \* rollout length
    MaxOperand,     \* bound on a positive input
    MaxDeficit,     \* bound on a NEGATIVE input, the case a floor must kill
    GapMax          \* integer stand-in for tau*ln2

ASSUME /\ MaxSteps   \in Nat
       /\ MaxOperand \in Nat
       /\ MaxDeficit \in Nat
       /\ GapMax     \in Nat

VARIABLES
    t,              \* step counter (the rollout clock)
    hardStock,      \* accumulator fed by the EXACT floor max(x, 0)
    softStock,      \* accumulator fed by the OVERSHOOTING smooth_relu
    lastIn,         \* input to the most recent application
    lastOut,        \* smooth_relu result of the most recent application
    phantom,        \* TRUE once a should-be-zero input yielded a positive value
    allNonPos       \* TRUE while every input so far has been <= 0

vars == <<t, hardStock, softStock, lastIn, lastOut, phantom, allNonPos>>

Max(a, b) == IF a >= b THEN a ELSE b

\* The exact floor, and the overshooting operator that stands in for it.
HardRelu(x)      == Max(x, 0)
SmoothRelu(x, d) == Max(x, 0) + d

Inputs == (0 - MaxDeficit)..MaxOperand
Gaps   == 0..GapMax

MaxTrue    == MaxOperand * MaxSteps
MaxPhantom == GapMax * MaxSteps

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t         \in 0..MaxSteps
    /\ hardStock \in 0..MaxTrue
    /\ softStock \in 0..(MaxTrue + MaxPhantom)
    /\ lastIn    \in Inputs
    /\ lastOut   \in 0..(MaxOperand + GapMax)
    /\ phantom   \in BOOLEAN
    /\ allNonPos \in BOOLEAN

\* -- Initial state -------------------------------------------------------
Init ==
    /\ t         = 0
    /\ hardStock = 0
    /\ softStock = 0
    /\ lastIn    = 0
    /\ lastOut   = 0
    /\ phantom   = FALSE
    /\ allNonPos = TRUE

\* -- Actions -------------------------------------------------------------
\* One step of the rollout.  The input may be negative (the case a floor at
\* zero exists to kill), the gap is adversarial within its guaranteed bound,
\* and both accumulators are advanced from the SAME input.
Step(x, d) ==
    /\ t < MaxSteps
    /\ t' = t + 1
    /\ LET hard == HardRelu(x)
           soft == SmoothRelu(x, d)
       IN  /\ lastIn'    = x
           /\ lastOut'   = soft
           /\ hardStock' = hardStock + hard
           /\ softStock' = softStock + soft
           \* Bracketed: "=" binds tighter than "\/" and "/\". Unbracketed,
           \* the first leaves phantom' unconstrained (a TLC error) and the
           \* second silently pins allNonPos' and gates the whole action on
           \* x =< 0, shrinking the state space with no error at all.
           /\ phantom'   = (phantom \/ (x =< 0 /\ soft > 0))
           /\ allNonPos' = (allNonPos /\ (x =< 0))

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ \E x \in Inputs, d \in Gaps : Step(x, d)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* The defect is one-sided and UPWARD: softplus never returns less than the
\* exact floor.  Fails if the operator were modelled (or coded) with the gap
\* on the wrong side -- the SMOOTH-1 direction.
OvershootOneSided == lastOut >= HardRelu(lastIn)

\* The phantom is bounded by ONE tau*ln2 per application.  Fails if a call
\* site applies smooth_relu twice per step, or nests it inside another smooth
\* operator, without accounting for the compounding gap.
OvershootBounded == lastOut =< HardRelu(lastIn) + GapMax

\* The softplus accumulator may sit above the exact one but never below it.
NoPhantomLoss == softStock >= hardStock

\* Accumulated phantom is linear in rollout length, one gap per application,
\* never superlinear.  This is the tight bound: it is what fails first if a
\* phase applies the operator more than once per step.
PhantomAccumulationBounded == softStock =< hardStock + GapMax * t

\* A phantom cannot be undone downstream: once injected, the accumulator is
\* strictly positive for the rest of the rollout.  Fails if some path could
\* net the phantom back out.
PhantomIrreversible == phantom => softStock > 0

\* The EXACT floor holds the property the code needs: with every input
\* non-positive, the accumulator is exactly zero, not merely small.  Fails
\* the moment the exact-zero path is implemented with smooth_relu.
HardFloorExactAtZero == allNonPos => hardStock = 0

\* And the contrast that gives SMOOTH-2 its bite: on that same all-non-positive
\* history the softplus path is STRICTLY above the exact one, so a quantity
\* required to be exactly zero cannot be produced by smooth_relu.
PhantomIsReal == (allNonPos /\ phantom) => softStock > hardStock

\* -- Action properties ---------------------------------------------------
\* The economy genuinely evolves -- the clock ticks and the stocks move --
\* while the bounds above stay pinned.
SoftMonotone   == [][softStock' >= softStock]_vars
PhantomLatches == [][phantom => phantom']_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
