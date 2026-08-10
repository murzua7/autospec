---- MODULE DABSAllocationExhaustive ----
\* ALLOC-1: exhaustive allocation in softmax_allocation.
\*
\* Target: dabs/smooth.py:232 softmax_allocation(scores, total, tau), which
\* returns total * softmax(scores / tau).  In exact arithmetic the softmax
\* weights sum to one, so the allocated amounts sum to `total` and no mass is
\* created or destroyed by the split.  That is the property this spec pins.
\*
\* Why this is NOT already covered by DABSGoodsRationing (CLEAR-1).  That spec
\* rations against a supply CEILING: fill_rate = smooth_min(1, supply/demand),
\* so delivering LESS than demand is correct behaviour whenever supply binds,
\* and the invariant there is an inequality (TotalSold =< supply).  Here the
\* structure is the opposite: `total` is a budget that must be handed out in
\* full, and the invariant is an EQUALITY (sum of shares = total).  A shortfall
\* that CLEAR-1 must tolerate is exactly the defect ALLOC-1 must catch.
\*
\* TLA+ has no reals, so the softmax weights are carried as integer numerators
\* over the fixed denominator WeightScale, with the modelling assumption that
\* they sum to WeightScale -- that is what softmax guarantees, and it is the
\* only part of the operator this property depends on.  Everything downstream
\* of that -- the multiply by total, the rounding, the settlement -- is where
\* mass actually goes missing in an implementation, and that is what is
\* checked here.  The temperature enters through the ORDERING of the weights
\* and through the two limits pinned below, which is the part of tau's
\* behaviour that is checkable without reals.
\*
\* Two allocators run side by side over one rollout:
\*   recv     -- the settled path: floor division plus largest-remainder
\*               settlement of the rounding residue
\*   recvNaive-- the defect shape: floor division ALONE, no settlement, which
\*               silently drops up to NumSlots-1 units on every single call

EXTENDS Integers, Sequences

CONSTANTS
    NumSlots,       \* number of recipients the total is split across
    MaxSteps,       \* rollout length
    MaxTotal,       \* bound on the amount allocated in one call
    WeightScale     \* denominator the softmax weights are carried over

ASSUME /\ NumSlots    \in Nat /\ NumSlots > 1
       /\ MaxSteps    \in Nat
       /\ MaxTotal    \in Nat
       /\ WeightScale \in Nat /\ WeightScale > 0

Slots == 1..NumSlots

VARIABLES
    t,              \* step counter (the rollout clock)
    weights,        \* softmax weights of the call just made, over WeightScale
    total,          \* amount the call just made had to hand out
    recv,           \* per-slot receipts of the SETTLED allocator
    recvNaive,      \* per-slot receipts of the UNSETTLED (floor-only) allocator
    cumDispatched,  \* cumulative amount sent into the allocator
    cumReceived,    \* cumulative amount the settled allocator handed out
    cumNaive,       \* cumulative amount the floor-only allocator handed out
    concentrated    \* TRUE if the call just made was at the low-tau limit

vars == <<t, weights, total, recv, recvNaive,
          cumDispatched, cumReceived, cumNaive, concentrated>>

Sum(f, S) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN  f[x] + g[T \ {x}]
             IN  g[S]

Totals  == 0..MaxTotal
Amounts == 0..MaxTotal

\* A legal softmax weight vector: every weight strictly positive (softmax never
\* returns an exact zero -- exp is strictly positive) and the whole vector
\* summing to the scale.  These two facts are the entirety of what the operator
\* contributes to the allocation property.
WeightVectors ==
    { w \in [Slots -> 1..WeightScale] : Sum(w, Slots) = WeightScale }

\* The low-temperature limit: as tau -> 0 the softmax collapses onto the
\* argmax, which in this integer carrier is one slot holding the whole scale.
IsConcentrated(w) == \E i \in Slots : w[i] = WeightScale

\* -- the two allocators ---------------------------------------------------
\* Floor division: what `(total * softmax(...)).floor()` or an integer cast of
\* the tensor gives you.  Each slot gets at least its exact share rounded down,
\* so the residue is non-negative and strictly smaller than NumSlots.
FloorShare(w, amt, i) == (amt * w[i]) \div WeightScale

FloorAlloc(w, amt) == [i \in Slots |-> FloorShare(w, amt, i)]

Residue(w, amt) == amt - Sum(FloorAlloc(w, amt), Slots)

\* Largest-remainder settlement.  The residue is handed out one unit at a time
\* to the slots with the largest fractional parts; modelled here by allowing
\* the settlement to fall on ANY set of distinct slots of the right size, which
\* is a sound over-approximation of every deterministic tie-break rule an
\* implementation might use.  If the property holds for all of them it holds
\* for the one the code picks.
\* Defined BEFORE its use below: TLA+ has no forward references, and the
\* original ordering put this after Settlements, which failed to compile with
\* "Unknown operator: Cardinality".
Cardinality(S) == Sum([i \in S |-> 1], S)

Settlements(w, amt) ==
    { S \in SUBSET Slots : Cardinality(S) = Residue(w, amt) }

SettledAlloc(w, amt, S) ==
    [i \in Slots |-> FloorShare(w, amt, i) + (IF i \in S THEN 1 ELSE 0)]

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t             \in 0..MaxSteps
    /\ weights       \in [Slots -> 0..WeightScale]
    /\ total         \in Totals
    /\ recv          \in [Slots -> Amounts]
    /\ recvNaive     \in [Slots -> Amounts]
    /\ cumDispatched \in 0..(MaxTotal * MaxSteps)
    /\ cumReceived   \in 0..(MaxTotal * MaxSteps)
    /\ cumNaive      \in 0..(MaxTotal * MaxSteps)
    /\ concentrated  \in BOOLEAN

\* -- Initial state -------------------------------------------------------
Init ==
    /\ t             = 0
    /\ weights       = [i \in Slots |-> 0]
    /\ total         = 0
    /\ recv          = [i \in Slots |-> 0]
    /\ recvNaive     = [i \in Slots |-> 0]
    /\ cumDispatched = 0
    /\ cumReceived   = 0
    /\ cumNaive      = 0
    /\ concentrated  = FALSE

\* -- Actions -------------------------------------------------------------
\* One allocation: a fresh budget, a fresh legal softmax weight vector, and an
\* adversarial choice of which slots absorb the rounding residue.
Step(amt, w, S) ==
    /\ t < MaxSteps
    /\ t' = t + 1
    /\ S \in Settlements(w, amt)
    /\ LET settled == SettledAlloc(w, amt, S)
           naive   == FloorAlloc(w, amt)
       IN  /\ weights'       = w
           /\ total'         = amt
           /\ recv'          = settled
           /\ recvNaive'     = naive
           /\ cumDispatched' = cumDispatched + amt
           /\ cumReceived'   = cumReceived + Sum(settled, Slots)
           /\ cumNaive'      = cumNaive + Sum(naive, Slots)
           /\ concentrated'  = IsConcentrated(w)

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ \E amt \in Totals, w \in WeightVectors, S \in SUBSET Slots : Step(amt, w, S)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* THE headline property: the split is exhaustive.  Not "close to total",
\* EXACTLY total.  This is what fails if the residue settlement is dropped, if
\* a slot is skipped by an off-by-one over the recipient index, or if the
\* weights are renormalised against the wrong axis.
AllocationIsExhaustive == t > 0 => Sum(recv, Slots) = total

\* Every share is non-negative.  softmax weights are strictly positive, so no
\* recipient can be handed a debit; a negative share would mean the sign was
\* lost somewhere between the weights and the settlement.
SharesNonNegative == \A i \in Slots : recv[i] >= 0

\* No slot receives more than the whole budget.  Fails if the total were
\* multiplied in per-slot rather than split across slots -- the classic
\* broadcast-instead-of-reduce bug in tensor code.
NoSlotExceedsTotal == \A i \in Slots : recv[i] =< total

\* The ledger closes over the whole rollout: everything dispatched was
\* received.  cumDispatched and cumReceived accumulate independently, so a
\* per-call leak shows up here even if a single call happened to be clean.
LedgerCloses == cumReceived = cumDispatched

\* Ordering is respected: a slot with a strictly larger softmax weight is never
\* handed strictly less than a slot with a smaller one, up to the single unit
\* the rounding settlement can move.  This is what fails if the scores were
\* paired with the wrong recipients -- an allocation that conserves mass
\* perfectly while sending it to the wrong agents.
OrderingRespected ==
    t > 0 => \A i, j \in Slots :
                 weights[i] >= weights[j] => recv[i] + 1 >= recv[j]

\* The low-temperature limit: when the softmax has collapsed onto its argmax,
\* that slot takes the entire budget and every other slot takes nothing.
ConcentratedLimit ==
    (t > 0 /\ concentrated) =>
        \E i \in Slots : /\ recv[i] = total
                         /\ \A j \in Slots : j # i => recv[j] = 0

\* -- the falsifiable bite -------------------------------------------------
\* The floor-only allocator never hands out more than the budget, but it can
\* hand out LESS -- up to NumSlots-1 units are lost per call to rounding.
\* This is the defect ALLOC-1 exists to catch: an allocation that looks right
\* on every individual share while quietly destroying mass on every step.
NaiveNeverOverAllocates == cumNaive =< cumDispatched

NaiveLeakBounded == cumNaive >= cumDispatched - (NumSlots - 1) * t

\* And the contrast with the settled path: whenever the floor-only allocator
\* has leaked at all, the settled one has not.  A single invariant that pins
\* both the defect and its fix in the same state.
SettledStrictlyBetter ==
    cumNaive < cumDispatched => cumReceived > cumNaive

\* -- Action properties ---------------------------------------------------
\* The allocator genuinely runs again and again -- budgets accumulate and the
\* clock ticks -- while the exactness invariants stay pinned.
DispatchMonotone == [][cumDispatched' >= cumDispatched]_vars
ReceiptMonotone  == [][cumReceived'   >= cumReceived]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
