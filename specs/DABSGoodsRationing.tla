---- MODULE DABSGoodsRationing ----
\* CLEAR-1: whole-market rationing conservation in GoodsMarket.clear.
\*
\* Target: dabs/markets/goods.py:28 GoodsMarket.clear (same mechanism in the
\* production mirror dabs/approaches/batched/markets/goods.py).  Mechanism, as
\* transcribed from the code at e6daf7c:
\*     ratio     = total_demand / (supply + EPS)
\*     fill_rate = smooth_min(1, 1 / (ratio + EPS))
\* and every buyer class -- firm intermediate demand, household consumption,
\* government purchases -- receives demand * fill_rate, pro rata.
\*
\* TLA+ has no reals, so the fill rate is carried as a NUMERATOR over the fixed
\* denominator FillScale, and smooth_min is modelled as its exact counterpart
\* MINUS a bounded nondeterministic gap g \in 0..GapMax, with GapMax the integer
\* stand-in for tau*ln2.  That is exactly the guarantee the operator gives; the
\* same abstraction underpins DABSSmoothMinEscape (SMOOTH-1).  Per-class shares
\* use floor division, which is the conservative rounding direction: it can only
\* under-fill, never oversell.
\*
\* The market is cleared repeatedly against a fresh supply and fresh demands, so
\* the economy genuinely evolves while the conservation invariants stay pinned.

EXTENDS Integers

CONSTANTS
    MaxSteps,       \* rollout length
    MaxSupply,      \* bound on available supply in one clearing
    MaxDemand,      \* bound on one buyer class's demand
    FillScale,      \* denominator the fill rate is carried over (1 == full fill)
    GapMax          \* integer stand-in for tau*ln2, scaled by FillScale

ASSUME /\ MaxSteps  \in Nat
       /\ MaxSupply \in Nat
       /\ MaxDemand \in Nat
       /\ FillScale \in Nat /\ FillScale > 0
       /\ GapMax    \in 0..FillScale

VARIABLES
    t,              \* step counter (the clearing clock)
    supply,         \* supply available to the clearing just performed
    d1, d2, d3,     \* demand of firm intermediate / household / government
    r1, r2, r3,     \* realised purchases of the same three classes
    fillNum,        \* fill rate actually applied, over FillScale
    lastGap,        \* smooth_min undershoot used by the clearing just performed
    cumSupply,      \* cumulative supply offered over the rollout
    cumSold,        \* cumulative goods handed over
    cumDemand,      \* cumulative demand presented
    cumUnmet        \* cumulative residual, accumulated PER CLASS

vars == <<t, supply, d1, d2, d3, r1, r2, r3, fillNum, lastGap,
          cumSupply, cumSold, cumDemand, cumUnmet>>

Min(a, b) == IF a =< b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

Supplies == 0..MaxSupply
Demands  == 0..MaxDemand
Gaps     == 0..GapMax

TotalDemand == d1 + d2 + d3
TotalSold   == r1 + r2 + r3

\* min(1, supply/total_demand), carried over FillScale.  Floor division is the
\* safe direction: it under-states the rate rather than over-stating it.
ExactFill(s, D) == IF D = 0 THEN FillScale
                            ELSE Min(FillScale, (FillScale * s) \div D)

\* The rate the code actually applies: the exact rate, undershot by the gap.
SmoothFill(s, D, g) == Max(0, ExactFill(s, D) - g)

\* demand * fill_rate, pro rata, rounded down.
Share(d, f) == (d * f) \div FillScale

AmpleSupply == supply >= TotalDemand

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t         \in 0..MaxSteps
    /\ supply    \in Supplies
    /\ d1 \in Demands /\ d2 \in Demands /\ d3 \in Demands
    /\ r1 \in Demands /\ r2 \in Demands /\ r3 \in Demands
    /\ fillNum   \in 0..FillScale
    /\ lastGap   \in Gaps
    /\ cumSupply \in 0..(MaxSupply * MaxSteps)
    /\ cumSold   \in 0..(MaxSupply * MaxSteps)
    /\ cumDemand \in 0..(3 * MaxDemand * MaxSteps)
    /\ cumUnmet  \in 0..(3 * MaxDemand * MaxSteps)

\* -- Initial state -------------------------------------------------------
Init ==
    /\ t         = 0
    /\ supply    = 0
    /\ d1 = 0 /\ d2 = 0 /\ d3 = 0
    /\ r1 = 0 /\ r2 = 0 /\ r3 = 0
    /\ fillNum   = FillScale
    /\ lastGap   = 0
    /\ cumSupply = 0
    /\ cumSold   = 0
    /\ cumDemand = 0
    /\ cumUnmet  = 0

\* -- Actions -------------------------------------------------------------
\* One clearing: fresh supply, fresh demand from each of the three classes,
\* an adversarial gap within the operator's guaranteed bound, and a single
\* shared fill rate applied to all three classes.
Step(s, a, b, c, g) ==
    /\ t < MaxSteps
    /\ t' = t + 1
    /\ LET D  == a + b + c
           f  == SmoothFill(s, D, g)
           x1 == Share(a, f)
           x2 == Share(b, f)
           x3 == Share(c, f)
       IN  /\ supply' = s
           /\ d1' = a /\ d2' = b /\ d3' = c
           /\ r1' = x1 /\ r2' = x2 /\ r3' = x3
           /\ fillNum' = f
           /\ lastGap' = g
           /\ cumSupply' = cumSupply + s
           /\ cumSold'   = cumSold + x1 + x2 + x3
           /\ cumDemand' = cumDemand + D
           /\ cumUnmet'  = cumUnmet + (a - x1) + (b - x2) + (c - x3)

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ \E s \in Supplies, a, b, c \in Demands, g \in Gaps : Step(s, a, b, c, g)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* The rate never exceeds full fill.  Fails if the min against 1 were dropped,
\* or if the smooth operator were on the overshooting side (smooth_relu), in
\* which case an ample market would hand out MORE than was demanded.
FillNeverExceedsFull == fillNum =< FillScale

\* No class receives more than it asked for.
NoClassOverFilled == /\ r1 =< d1
                     /\ r2 =< d2
                     /\ r3 =< d3

\* No goods are created in a single clearing: the three classes together never
\* take more than the supply on offer.  This is the invariant that fails if the
\* denominator total_demand is built from a SUBSET of the buyer classes -- for
\* instance government purchases filled but not counted -- because the fill rate
\* is then too high and the market oversells.
NoGoodsCreated == TotalSold =< supply

\* The same, across the whole rollout: cumulative deliveries never outrun
\* cumulative supply.
NoOverSaleCumulative == cumSold =< cumSupply

\* Every class is rationed by the SAME rate -- no class jumps the queue.  The
\* upper bound fails if any class is served ahead of the others at full demand;
\* the tightness bound fails if a class is served at less than the shared rate,
\* i.e. silently dropped mass.  Together they pin each class to one rate within
\* a single unit of rounding, which implies pairwise pro-rata fairness.
UniformFillUpper == /\ r1 * FillScale =< d1 * fillNum
                    /\ r2 * FillScale =< d2 * fillNum
                    /\ r3 * FillScale =< d3 * fillNum

UniformFillTight == /\ r1 * FillScale + FillScale > d1 * fillNum
                    /\ r2 * FillScale + FillScale > d2 * fillNum
                    /\ r3 * FillScale + FillScale > d3 * fillNum

\* Unmet demand is conserved as a residual: what was asked for was either
\* delivered or left unmet, never lost and never double-counted.  cumUnmet is
\* accumulated from the PER-CLASS residuals while cumSold and cumDemand are
\* accumulated from totals, so a residual booked against the wrong base breaks
\* the identity.
ResidualConserved == cumSold + cumUnmet = cumDemand

ResidualNonNegative == cumUnmet >= 0

\* The smooth-operator consequence.  Because smooth_min undershoots -- most
\* severely at a = b, which is exactly market balance -- the market rations even
\* when supply is ample.  The shortfall is bounded by one gap per clearing.
ShortfallUnderAmpleSupplyBounded ==
    AmpleSupply => /\ d1 - r1 =< ((d1 * GapMax) \div FillScale) + 1
                   /\ d2 - r2 =< ((d2 * GapMax) \div FillScale) + 1
                   /\ d3 - r3 =< ((d3 * GapMax) \div FillScale) + 1

\* And the bite: with supply ample and any gap at all, realised purchases are
\* STRICTLY below demand.  Phantom rationing of a market that could have been
\* cleared in full -- output lost to the smoothing, not to scarcity.
PhantomRationingIsReal ==
    (AmpleSupply /\ TotalDemand > 0 /\ lastGap > 0) => TotalSold < TotalDemand

\* -- Action properties ---------------------------------------------------
\* The market genuinely clears again and again while the bounds stay pinned.
SoldMonotone  == [][cumSold'  >= cumSold]_vars
UnmetMonotone == [][cumUnmet' >= cumUnmet]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
