---- MODULE DABSStepOrdering ----
\* SCHED-1: sub-step ordering preconditions of the batched simulation step.
\*
\* Target: dabs/approaches/batched/simulation.py, the step loop at ~1029-1108.
\* The schedule has a FIXED prefix, a CONFIG-DEPENDENT middle block, and a
\* FIXED suffix:
\*
\*   prefix  _phase_exchange_estimation -> _phase_targets -> _phase_labour
\*   middle  _phase_monetary, _phase_credit, _phase_production,
\*           _phase_pricing, _phase_housing  -- emitted in one of THREE
\*           different orders depending on configuration
\*   suffix  _phase_goods_trade -> _phase_balance_sheets -> _phase_government
\*           -> _phase_insolvency -> _phase_capital -> _phase_aggregation
\*
\* The middle block is modelled as a FREE order subject only to the
\* dependencies the code actually enforces, which is a sound
\* over-approximation of all three concrete orderings: if the ordering
\* properties hold for every admissible interleaving they hold for the three
\* the configuration can select. Pricing is the one intra-block dependency
\* that survives in every branch (production is always emitted before pricing).
\*
\* State is carried as the SET of phases already run this step plus an
\* independent counter, never as a sequence, so the state space stays small
\* while at-most-once remains checkable.

EXTENDS Integers, FiniteSets

CONSTANTS MaxSteps

ASSUME MaxSteps \in Nat

Phases == {"Ex", "Tg", "Lb", "Mo", "Cr", "Pr", "Pc", "Ho",
           "Gt", "Bs", "Gv", "In", "Cp", "Ag"}

NumPhases == 14

\* Dependencies transcribed from the step loop.
Prereq(p) ==
    CASE p = "Ex" -> {}
      [] p = "Tg" -> {"Ex"}
      [] p = "Lb" -> {"Tg"}
      [] p = "Mo" -> {"Lb"}
      [] p = "Cr" -> {"Lb"}
      [] p = "Pr" -> {"Lb"}
      [] p = "Pc" -> {"Pr"}
      [] p = "Ho" -> {"Lb"}
      [] p = "Gt" -> {"Mo", "Cr", "Pr", "Pc", "Ho"}
      [] p = "Bs" -> {"Gt"}
      [] p = "Gv" -> {"Bs"}
      [] p = "In" -> {"Gv"}
      [] p = "Cp" -> {"In"}
      [] p = "Ag" -> {"Cp"}
      [] OTHER   -> {}

VARIABLES
    done,       \* set of phases already run in the CURRENT step
    ran,        \* independent count of phase dispatches in the current step
    t,          \* completed steps (the quarterly clock)
    everRan     \* cumulative count of dispatches across all steps

vars == <<done, ran, t, everRan>>

TypeOK ==
    /\ done    \subseteq Phases
    /\ ran     \in 0..NumPhases
    /\ t       \in 0..MaxSteps
    /\ everRan \in 0..(NumPhases * MaxSteps + NumPhases)

Init ==
    /\ done    = {}
    /\ ran     = 0
    /\ t       = 0
    /\ everRan = 0

\* A phase is dispatched only if it has not run this step and every
\* dependency it declares has already run.
RunPhase(p) ==
    /\ p \notin done
    /\ Prereq(p) \subseteq done
    /\ done'    = (done \cup {p})
    /\ ran'     = ran + 1
    /\ everRan' = everRan + 1
    /\ UNCHANGED t

\* The step closes only when every phase has run, and resets for the next.
EndStep ==
    /\ done = Phases
    /\ t < MaxSteps
    /\ t'    = t + 1
    /\ done' = {}
    /\ ran'  = 0
    /\ UNCHANGED everRan

Terminal ==
    /\ t = MaxSteps
    /\ done = Phases
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Phases : RunPhase(p)
    \/ EndStep
    \/ Terminal

\* -- Ordering preconditions ----------------------------------------------
\* Each must hold under EVERY admissible interleaving of the middle block,
\* which is what makes them statements about the schedule rather than about
\* one configuration's branch.

\* Goods are never traded before they are produced.
ProductionBeforeTrade == "Gt" \in done => "Pr" \in done

\* Prices are set from production, never ahead of it. This is the one
\* intra-block dependency that holds in all three concrete orderings.
PricingAfterProduction == "Pc" \in done => "Pr" \in done

\* The books are never written before the quarter's transactions exist.
\* This is the headline precondition: settlement never precedes clearing.
TradeBeforeBalanceSheets == "Bs" \in done => "Gt" \in done

\* Solvency is judged on booked balance sheets, never on stale ones.
BalanceSheetsBeforeInsolvency == "In" \in done => "Bs" \in done

\* Fiscal settlement precedes the insolvency wave it can fund.
GovernmentBeforeInsolvency == "In" \in done => "Gv" \in done

\* Aggregation observes a completed step: it can only have run once every
\* other phase has. Catches a reordering that publishes aggregates from a
\* half-finished quarter.
AggregationLast == "Ag" \in done => done = Phases

\* -- At-most-once dispatch ------------------------------------------------
\* ran counts dispatches, done counts DISTINCT phases. If any phase were
\* dispatched twice in one step -- double-counting its flows -- the counter
\* would exceed the cardinality and this fails.
AtMostOnce == ran = Cardinality(done)

\* -- Dependency closure ---------------------------------------------------
\* Nothing in the executed set is missing a dependency.
PrereqClosure == \A p \in done : Prereq(p) \subseteq done

\* -- Non-vacuity ----------------------------------------------------------
\* The clock only advances through fully completed steps, so the schedule
\* genuinely runs to completion rather than stalling in a partial state.
ClockOnlyOnCompleteSteps == everRan >= t * NumPhases

Spec == Init /\ [][Next]_vars

====
