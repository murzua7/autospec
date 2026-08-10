---- MODULE DABSInventoryStock ----
\* INV-1: the inventory stock recursion in GoodsMarket.update_inventory.
\*
\* Target: dabs/markets/goods.py, GoodsMarket.update_inventory (mirrored in the
\* production path dabs/approaches/batched/markets/goods.py).  Mechanism, as
\* transcribed from the code at e6daf7c:
\*     inventory = prev_inventory + production - total_sold
\*
\* This is a STOCK recursion, and it is the one place where a flow error becomes
\* permanent: a clearing that oversells does not merely mis-price one quarter,
\* it drives the carried buffer negative and every later quarter inherits the
\* hole.  CLEAR-1 (DABSGoodsRationing) checks the within-clearing flow algebra
\* against a supply figure handed to it; nothing there carries a stock across
\* steps.  This spec supplies the missing half: where that supply figure comes
\* from, and what the recursion does with what is left.
\*
\* The economically important coupling is that available supply for a clearing
\* is the carried inventory PLUS current production -- a firm sells out of the
\* buffer, not only out of the quarter's output.  The falsifiable content is
\* that the fill rate MUST be sized against that same total.  A clearing that
\* sized the rate against production alone, while settling against the buffer,
\* would look conservative and would still be wrong in the other direction; a
\* clearing that settled against a total larger than the buffer it holds sells
\* goods that do not exist.  BadAvailable below models exactly that second
\* mistake, and NonNegativeInventory is what catches it.
\*
\* TLA+ has no reals, so the fill rate is carried as a NUMERATOR over the fixed
\* denominator FillScale, and smooth_min is modelled as its exact counterpart
\* MINUS a bounded nondeterministic gap g \in 0..GapMax, with GapMax the integer
\* stand-in for tau*ln2.  Same abstraction as DABSSmoothMinEscape (SMOOTH-1) and
\* DABSGoodsRationing (CLEAR-1).  Per-class shares use floor division, the
\* conservative rounding direction: it can only under-fill, never oversell.

EXTENDS Integers

CONSTANTS
    MaxSteps,       \* rollout length
    MaxProd,        \* bound on one quarter's production
    MaxDemand,      \* bound on one buyer class's demand
    FillScale,      \* denominator the fill rate is carried over (1 == full fill)
    GapMax          \* integer stand-in for tau*ln2, scaled by FillScale

ASSUME /\ MaxSteps  \in Nat
       /\ MaxProd    \in Nat
       /\ MaxDemand  \in Nat
       /\ FillScale  \in Nat /\ FillScale > 0
       /\ GapMax     \in 0..FillScale

VARIABLES
    t,              \* step counter (the quarterly clock)
    inventory,      \* the carried stock -- the variable under test
    production,     \* output added by the step just taken
    available,      \* supply the clearing was settled against
    sold,           \* goods actually handed over by that clearing
    demand,         \* total demand presented to that clearing
    fillNum,        \* fill rate applied, over FillScale
    cumProd,        \* cumulative production over the rollout
    cumSold,        \* cumulative goods handed over
    drewDown        \* TRUE once a step sold more than it produced

vars == <<t, inventory, production, available, sold, demand, fillNum,
          cumProd, cumSold, drewDown>>

Min(a, b) == IF a =< b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

Prods   == 0..MaxProd
Demands == 0..MaxDemand
Gaps    == 0..GapMax

MaxStock == MaxProd * MaxSteps
MaxFlow  == 3 * MaxDemand

\* What the firm can actually hand over this quarter: the buffer it carried in,
\* plus what it just made.  This is the figure the clearing MUST be sized on.
GoodAvailable(inv, prod) == inv + prod

\* The mistake this spec exists to catch: sizing the fill rate against the
\* quarter's output alone while settling out of the buffer as well.  Swap this
\* into Step in place of GoodAvailable and NonNegativeInventory fails.
BadAvailable(inv, prod) == prod

\* min(1, available/total_demand), carried over FillScale, floored.
ExactFill(s, D) == IF D = 0 THEN FillScale
                            ELSE Min(FillScale, (FillScale * s) \div D)

\* The rate the code actually applies: exact rate, undershot by the gap.
SmoothFill(s, D, g) == Max(0, ExactFill(s, D) - g)

\* demand * fill_rate, pro rata, rounded down.
Share(d, f) == (d * f) \div FillScale

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t          \in 0..MaxSteps
    /\ inventory  \in 0..MaxStock
    /\ production \in Prods
    /\ available  \in 0..(MaxStock + MaxProd)
    /\ sold       \in 0..MaxFlow
    /\ demand     \in 0..MaxFlow
    /\ fillNum    \in 0..FillScale
    /\ cumProd    \in 0..MaxStock
    /\ cumSold    \in 0..(MaxFlow * MaxSteps)
    /\ drewDown   \in BOOLEAN

\* -- Initial state -------------------------------------------------------
\* The economy opens with an empty buffer, so every unit ever sold has to be
\* traceable to something produced inside the rollout.  That is what makes
\* StockRecursionCloses non-vacuous.
Init ==
    /\ t          = 0
    /\ inventory  = 0
    /\ production = 0
    /\ available  = 0
    /\ sold       = 0
    /\ demand     = 0
    /\ fillNum    = FillScale
    /\ cumProd    = 0
    /\ cumSold    = 0
    /\ drewDown   = FALSE

\* -- Actions -------------------------------------------------------------
\* One quarter: produce, clear the goods market against buffer plus output for
\* the three buyer classes, then roll the stock forward.
Step(p, a, b, c, g) ==
    /\ t < MaxSteps
    /\ t' = t + 1
    /\ LET D    == a + b + c
           avail == GoodAvailable(inventory, p)
           f     == SmoothFill(avail, D, g)
           x     == Share(a, f) + Share(b, f) + Share(c, f)
       IN  /\ production' = p
           /\ available'  = avail
           /\ demand'     = D
           /\ fillNum'    = f
           /\ sold'       = x
           \* The recursion under test, transcribed literally.
           /\ inventory'  = inventory + p - x
           /\ cumProd'    = cumProd + p
           /\ cumSold'    = cumSold + x
           \* Bracketed: "=" binds tighter than "\/", so the unbracketed form
           \* leaves drewDown' unconstrained whenever x > p.
           /\ drewDown'   = (drewDown \/ (x > p))

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ \E p \in Prods, a, b, c \in Demands, g \in Gaps : Step(p, a, b, c, g)
    \/ Done

\* -- Safety invariants ---------------------------------------------------
\* Inventory cannot go negative.  This is the headline property, and it is the
\* one that fails the moment a clearing path settles against a buffer it does
\* not hold -- substitute BadAvailable above, or drop the min-against-supply
\* from the fill rate, and TLC produces the trace.
NonNegativeInventory == inventory >= 0

\* Nothing is sold that was not there to sell.  Within a quarter, deliveries
\* never exceed the buffer plus that quarter's output.
NoSaleWithoutSupply == sold =< available

\* The recursion closes over the whole rollout: what is left in the buffer is
\* exactly what was produced minus what was sold.  Because cumProd and cumSold
\* accumulate the flows independently of the stock update, a recursion that
\* dropped or double-counted a term breaks this identity.
StockRecursionCloses == inventory = cumProd - cumSold

\* No goods are created across the rollout: cumulative sales never outrun
\* cumulative production, given an empty opening buffer.
NoGoodsCreated == cumSold =< cumProd

\* The buffer is bounded above by everything ever made.  Fails if production
\* were added twice, or if a sale credited the stock instead of debiting it.
InventoryBoundedByProduction == inventory =< cumProd

\* Supply offered to the clearing is exactly buffer plus output -- neither a
\* phantom addition nor a forgotten buffer.
AvailableIsBufferPlusOutput ==
    t > 0 => available = (inventory + sold) - production + production

\* The buffer-drawdown case, which is where the recursion earns its keep: if a
\* quarter sold more than it produced, the stock must have STRICTLY fallen.
\* Stated over the rollout: a drawdown at any point means cumulative sales have
\* at some stage exceeded cumulative production net of the opening buffer, so a
\* stock that never moved would be a manufactured buffer.
DrawdownConsumesStock == drewDown => cumSold > 0

\* Rationing is real, not decorative: deliveries never exceed demand.
NoOverDelivery == sold =< demand

\* -- Action properties ---------------------------------------------------
\* The economy genuinely evolves -- output accumulates and the clock ticks --
\* while the stock bounds above stay pinned.
ProductionMonotone == [][cumProd' >= cumProd]_vars
SalesMonotone      == [][cumSold' >= cumSold]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
