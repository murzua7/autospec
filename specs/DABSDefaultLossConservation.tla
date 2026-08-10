---- MODULE DABSDefaultLossConservation ----
\* DEF-1: loss conservation and the exit cap in _phase_insolvency.
\*
\* Target: dabs/approaches/batched/simulation.py:3596 _phase_insolvency.
\* Mechanism, as transcribed from the code at e6daf7c: compute_default returns
\* an insolvency probability CAPPED at config.max_quarterly_firm_exit; a
\* write-off reduces BOTH sides of the loan contract -- the firm's debt
\* disappears AND the bank's asset is written down -- and the seized firm
\* deposits are booked as NPL recovery.
\*
\* Why this is NOT already covered by DABSSFCBalance (SFC-1).  That spec has a
\* WriteOff posting, but it is a bare principal cancellation: the claim is
\* absorbed by capital in full, there is no seizure of the failing firm's
\* deposits, no partition of the unpaid claim into a recovered part and a lost
\* part, no firm population and no per-quarter exit budget.  DEF-1's content is
\* exactly the part SFC-1 leaves out -- WHERE the write-down lands and HOW MUCH
\* of it the bank gets back -- and a model can keep its balance sheet closing
\* perfectly while booking the recovery twice or seizing money the firm never
\* held.  DABSMoneyEndogenous (MONEY-1) declines write-offs outright in its own
\* scope note, because they move deposits and loans outside the lend/repay pair.
\*
\* The modelling decisions that make this non-vacuous:
\*
\*   1. bankEquity is an INDEPENDENT variable, moved only by the loss leg of a
\*      write-off.  Recomputing it as assets minus liabilities would turn the
\*      closure invariant into a tautology no coding error could break.
\*   2. The exit cap is NOT simply asserted on a set the spec already built to
\*      satisfy it.  Each quarter draws a DESIRED exit set D -- what
\*      compute_default's uncapped probability would have retired -- and the
\*      realised set S is D filtered through the cap.  So the cap is a genuine
\*      selection with observable consequences: firms that wanted to exit and
\*      did not are counted as deferred, and the deferral is conserved.
\*   3. The cap denominator is the ALIVE population, not the firm count.  A
\*      cap applied against the wrong denominator is a real and easy defect --
\*      it lets the exit rate drift above the configured ceiling as the
\*      population shrinks -- and ExitRateWithinCap is what catches it.
\*
\* Exits are not gated on insolvency here.  compute_default returns a
\* PROBABILITY, so a solvent firm can be drawn out; admitting every alive firm
\* is the conservative direction, and a conservation law that holds for all of
\* them holds for the ones the code actually picks.

EXTENDS Integers, FiniteSets

CONSTANTS
    NumFirms,       \* size of the firm population
    MaxSteps,       \* rollout length in quarters
    MaxAmount,      \* bound on one lending or spending posting
    InitEquity,     \* opening bank capital, held against government bonds
    ExitCapNum,     \* config.max_quarterly_firm_exit, numerator
    ExitCapDen      \* ... over this denominator

ASSUME /\ NumFirms   \in Nat /\ NumFirms > 1
       /\ MaxSteps   \in Nat /\ MaxSteps > 2
       /\ MaxAmount  \in Nat /\ MaxAmount > 0
       /\ InitEquity \in Nat
       /\ ExitCapDen \in Nat /\ ExitCapDen > 0
       /\ ExitCapNum \in 0..ExitCapDen

Firms == 1..NumFirms

VARIABLES
    t,              \* quarter counter (the rollout clock)
    alive,          \* per-firm liveness flag
    debt,           \* FIRM ledger: outstanding loan principal
    deposit,        \* FIRM ledger: deposit holding
    hh,             \* household deposit pot, so firms can spend below their debt
    bankLoans,      \* BANK ledger: loan asset, posted independently
    bankDeposits,   \* BANK ledger: deposit liability, posted independently
    bankBonds,      \* BANK ledger: the asset the opening capital is held against
    bankEquity,     \* BANK capital, INDEPENDENT, moved only by realised loss
    cumLent,        \* cumulative lending flow
    cumClaim,       \* cumulative unpaid claim extinguished by exits
    cumRecovery,    \* cumulative NPL recovery from seized deposits
    cumLoss,        \* cumulative loss absorbed by capital
    cumExits,       \* cumulative REALISED exits
    cumDesired,     \* cumulative exits the uncapped probability would have made
    cumDeferred,    \* cumulative exits the cap held back
    lastClaim,      \* the wave just processed: claim extinguished
    lastRecovery,   \* ... recovered from seized deposits
    lastLoss,       \* ... absorbed by capital
    lastSeizable,   \* ... deposits the exiting firms actually held
    lastExits,      \* ... realised exit count
    lastDesired,    \* ... desired exit count
    lastCap,        \* ... exit budget the cap allowed
    lastAlive,      \* ... alive population the cap was measured against
    shadowEquity,   \* shadow: capital debited by the FULL claim, recovery kept
    shadowLoans     \* shadow: firm debt cancelled, bank asset never written down

vars == <<t, alive, debt, deposit, hh, bankLoans, bankDeposits, bankBonds,
          bankEquity, cumLent, cumClaim, cumRecovery, cumLoss, cumExits,
          cumDesired, cumDeferred, lastClaim, lastRecovery, lastLoss,
          lastSeizable, lastExits, lastDesired, lastCap, lastAlive,
          shadowEquity, shadowLoans>>

Min(a, b) == IF a =< b THEN a ELSE b

Sum(f, S) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN  f[x] + g[T \ {x}]
             IN  g[S]

Total(f) == Sum(f, Firms)

Amounts  == 1..MaxAmount
Flow     == MaxAmount * MaxSteps
Counts   == 0..NumFirms
Waves    == 0..(NumFirms * MaxSteps)

AliveSet == {f \in Firms : alive[f]}

\* config.max_quarterly_firm_exit applied against the ALIVE population.
Cap == (ExitCapNum * Cardinality(AliveSet)) \div ExitCapDen

\* The three per-wave aggregates, all summed over the exiting set only.
ClaimOf(S)    == Sum([x \in Firms |-> IF x \in S THEN debt[x] ELSE 0], Firms)
SeizableOf(S) == Sum([x \in Firms |-> IF x \in S THEN deposit[x] ELSE 0], Firms)
SeizedOf(S)   == Sum([x \in Firms |->
                        IF x \in S THEN Min(deposit[x], debt[x]) ELSE 0], Firms)

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t            \in 0..MaxSteps
    /\ alive        \in [Firms -> BOOLEAN]
    /\ debt         \in [Firms -> 0..Flow]
    /\ deposit      \in [Firms -> 0..Flow]
    /\ hh           \in 0..Flow
    /\ bankLoans    \in 0..Flow
    /\ bankDeposits \in 0..Flow
    /\ bankBonds    \in 0..InitEquity
    /\ bankEquity   \in (InitEquity - Flow)..InitEquity
    /\ cumLent      \in 0..Flow
    /\ cumClaim     \in 0..Flow
    /\ cumRecovery  \in 0..Flow
    /\ cumLoss      \in 0..Flow
    /\ cumExits     \in Counts
    /\ cumDesired   \in Waves
    /\ cumDeferred  \in Waves
    /\ lastClaim    \in 0..Flow
    /\ lastRecovery \in 0..Flow
    /\ lastLoss     \in 0..Flow
    /\ lastSeizable \in 0..Flow
    /\ lastExits    \in Counts
    /\ lastDesired  \in Counts
    /\ lastCap      \in Counts
    /\ lastAlive    \in Counts
    /\ shadowEquity \in (InitEquity - 2 * Flow)..InitEquity
    /\ shadowLoans  \in 0..Flow

\* -- Initial state -------------------------------------------------------
\* The economy opens with every firm alive and debt-free, no deposits, and the
\* bank's capital held against government bonds, so the opening balance sheet
\* already closes with a non-zero asset side.
Init ==
    /\ t            = 0
    /\ alive        = [f \in Firms |-> TRUE]
    /\ debt         = [f \in Firms |-> 0]
    /\ deposit      = [f \in Firms |-> 0]
    /\ hh           = 0
    /\ bankLoans    = 0
    /\ bankDeposits = 0
    /\ bankBonds    = InitEquity
    /\ bankEquity   = InitEquity
    /\ cumLent      = 0
    /\ cumClaim     = 0
    /\ cumRecovery  = 0
    /\ cumLoss      = 0
    /\ cumExits     = 0
    /\ cumDesired   = 0
    /\ cumDeferred  = 0
    /\ lastClaim    = 0
    /\ lastRecovery = 0
    /\ lastLoss     = 0
    /\ lastSeizable = 0
    /\ lastExits    = 0
    /\ lastDesired  = 0
    /\ lastCap      = 0
    /\ lastAlive    = NumFirms
    /\ shadowEquity = InitEquity
    /\ shadowLoans  = 0

\* -- Actions -------------------------------------------------------------
\* Credit extension.  Present so that firms carry a claim worth writing off;
\* the loan asset and the deposit liability appear together.
Lend(f, amt) ==
    /\ alive[f]
    /\ debt'         = [debt    EXCEPT ![f] = @ + amt]
    /\ deposit'      = [deposit EXCEPT ![f] = @ + amt]
    /\ bankLoans'    = bankLoans + amt
    /\ bankDeposits' = bankDeposits + amt
    /\ cumLent'      = cumLent + amt
    /\ shadowLoans'  = shadowLoans + amt
    /\ shadowEquity' = shadowEquity
    /\ lastClaim'    = 0
    /\ lastRecovery' = 0
    /\ lastLoss'     = 0
    /\ lastSeizable' = 0
    /\ lastExits'    = 0
    /\ lastDesired'  = 0
    /\ lastCap'      = Cap
    /\ lastAlive'    = Cardinality(AliveSet)
    /\ UNCHANGED <<alive, hh, bankBonds, bankEquity, cumClaim, cumRecovery,
                   cumLoss, cumExits, cumDesired, cumDeferred>>

\* The firm spends its deposit into the household pot.  This is what makes the
\* LOSS leg reachable at all: without it every firm holds exactly its debt in
\* deposits, recovery always covers the claim in full, and cumLoss stays pinned
\* at zero -- the conservation law would then be checked only on its trivial
\* half.  The bank's deposit liability is untouched, so the money is relocated,
\* not destroyed.
Spend(f, amt) ==
    /\ alive[f]
    /\ deposit[f] >= amt
    /\ deposit'      = [deposit EXCEPT ![f] = @ - amt]
    /\ hh'           = hh + amt
    /\ lastClaim'    = 0
    /\ lastRecovery' = 0
    /\ lastLoss'     = 0
    /\ lastSeizable' = 0
    /\ lastExits'    = 0
    /\ lastDesired'  = 0
    /\ lastCap'      = Cap
    /\ lastAlive'    = Cardinality(AliveSet)
    /\ UNCHANGED <<alive, debt, bankLoans, bankDeposits, bankBonds, bankEquity,
                   cumLent, cumClaim, cumRecovery, cumLoss, cumExits,
                   cumDesired, cumDeferred, shadowEquity, shadowLoans>>

\* One quarter of _phase_insolvency.  D is what the uncapped insolvency
\* probability would have retired; S is what the cap actually lets through.
\* For each exiting firm the claim is split EXACTLY: the seized deposit up to
\* the claim is recovered, the remainder is a loss.  The bank asset is written
\* down by the WHOLE claim, the deposit liability by the recovery, and capital
\* absorbs only the loss -- three separate postings, none inferred from the
\* others.
ExitWave(D, S) ==
    /\ D # {}
    /\ D \subseteq AliveSet
    /\ S \subseteq D
    /\ Cardinality(S) = Min(Cardinality(D), Cap)
    /\ LET c == ClaimOf(S)
           r == SeizedOf(S)
           l == c - r
       IN  /\ alive'   = [f \in Firms |-> IF f \in S THEN FALSE ELSE alive[f]]
           /\ debt'    = [f \in Firms |-> IF f \in S THEN 0 ELSE debt[f]]
           /\ deposit' = [f \in Firms |->
                            IF f \in S
                            THEN deposit[f] - Min(deposit[f], debt[f])
                            ELSE deposit[f]]
           /\ bankLoans'    = bankLoans - c
           /\ bankDeposits' = bankDeposits - r
           /\ bankEquity'   = bankEquity - l
           /\ cumClaim'     = cumClaim + c
           /\ cumRecovery'  = cumRecovery + r
           /\ cumLoss'      = cumLoss + l
           /\ lastClaim'    = c
           /\ lastRecovery' = r
           /\ lastLoss'     = l
           \* The shadow that books the recovery AND still charges capital the
           \* whole claim: the recovered value is destroyed a second time.
           /\ shadowEquity' = shadowEquity - c
    /\ lastSeizable' = SeizableOf(S)
    /\ cumExits'     = cumExits + Cardinality(S)
    /\ cumDesired'   = cumDesired + Cardinality(D)
    /\ cumDeferred'  = cumDeferred + (Cardinality(D) - Cardinality(S))
    /\ lastExits'    = Cardinality(S)
    /\ lastDesired'  = Cardinality(D)
    /\ lastCap'      = Cap
    /\ lastAlive'    = Cardinality(AliveSet)
    \* The shadow that cancels the firm's debt and never writes the bank asset
    \* down: the one-sided write-off.
    /\ shadowLoans'  = shadowLoans
    /\ UNCHANGED <<hh, bankBonds, cumLent>>

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ /\ t < MaxSteps
       /\ t' = t + 1
       /\ \/ \E f \in Firms, a \in Amounts : Lend(f, a)
          \/ \E f \in Firms, a \in Amounts : Spend(f, a)
          \/ \E D \in SUBSET Firms, S \in SUBSET Firms : ExitWave(D, S)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* THE headline property: an exit creates and destroys nothing.  The unpaid
\* claim is split exactly into what the bank got back and what it lost.  This
\* fails if the seized deposit were booked as recovery while capital were still
\* charged the whole claim, or if the recovery were netted off the claim before
\* the loss was computed and then netted off again.
LossConservation      == cumRecovery + cumLoss = cumClaim
WaveLossConservation  == lastRecovery + lastLoss = lastClaim

\* Recovery cannot exceed what the failing firms actually held, nor what was
\* owed.  Fails if the seizure were sized against the claim rather than the
\* min of claim and balance -- an overdraft dressed up as a recovery.
RecoveryBoundedBySeizable == lastRecovery =< lastSeizable
RecoveryBoundedByClaim    == lastRecovery =< lastClaim
LossNonNegative           == lastLoss >= 0 /\ cumLoss >= 0

\* The realised exit rate never exceeds the configured ceiling, measured
\* against the ALIVE population.  A cap applied against the total firm count
\* instead would let the rate drift above the ceiling as the population
\* shrinks; this is the invariant that catches the wrong denominator.
ExitRateWithinCap == lastExits * ExitCapDen =< ExitCapNum * lastAlive

\* The cap is a real filter, not decoration: when more firms were drawn than
\* the budget allows, exactly the budget exits.
CapBindsWhenExceeded ==
    lastDesired > lastCap => lastExits = lastCap

\* ... and when the budget is slack, every drawn firm exits.  Fails if the cap
\* were applied unconditionally -- retiring a fixed quota every quarter whether
\* the probability called for it or not.
CapIsSlackWhenUnderBudget ==
    lastDesired =< lastCap => lastExits = lastDesired

\* Exits held back by the cap are conserved as a residual: drawn, not lost.
DeferralConserved   == cumDesired = cumExits + cumDeferred
RealisedWithinDesired == cumExits =< cumDesired

\* The two ledger mirrors.  A write-off that moved the bank leg and forgot the
\* firm leg, or scattered onto the wrong agent index, breaks these.
LoanLedgerMirrors    == bankLoans = Total(debt)
DepositLedgerMirrors == bankDeposits = Total(deposit) + hh

\* The bank balance sheet closes in every reachable state.  Non-vacuous
\* because bankEquity is posted, never recomputed.
BalanceSheetCloses == bankLoans + bankBonds = bankDeposits + bankEquity

\* Both stocks reconstruct from their flows.  Because the counters accumulate
\* independently of the stocks, a write-off booked twice, or a recovery applied
\* to the wrong side, breaks these while both mirrors could still look healthy.
LoanStockFromFlows   == bankLoans  = cumLent - cumClaim
EquityStockFromLosses == bankEquity = InitEquity - cumLoss

\* A retired firm carries no claim, and the population reconciles against the
\* exit counter.  Fails if an exit zeroed the bank asset but left the firm's
\* debt standing, so the same firm could be written off again next quarter.
DeadFirmsHoldNoDebt == \A f \in Firms : ~alive[f] => debt[f] = 0
AliveCountFromExits == Cardinality(AliveSet) = NumFirms - cumExits

\* The consequence of a cap strictly below one: the population can never be
\* wiped out in finite time, because the budget floors to zero once few enough
\* firms remain.  This is what a cap applied to a constant denominator loses.
SomeFirmAlwaysAlive == Cardinality(AliveSet) >= 1

StocksNonNegative ==
    /\ \A f \in Firms : debt[f]    >= 0
    /\ \A f \in Firms : deposit[f] >= 0
    /\ cumClaim =< cumLent

\* -- the falsifiable bite -------------------------------------------------
\* Shadow one: capital charged the FULL claim while the recovery is still
\* booked.  The recovered value is destroyed twice, so the shadow sits exactly
\* cumRecovery below the true capital.
DoubleCountIsExactlyRecovery == shadowEquity = bankEquity - cumRecovery

\* The error is one-sided and DOWNWARD: a double-counted recovery can only
\* understate capital, never overstate it.
DoubleCountUnderstatesCapital == shadowEquity =< bankEquity

\* And the consequence: the moment anything is recovered, the balance sheet
\* built on that capital figure no longer closes.  This is the state in which
\* the bank is silently writing off value it already has back.
DoubleCountBreaksClosure ==
    cumRecovery > 0 =>
        (bankLoans + bankBonds # bankDeposits + shadowEquity)

\* Shadow two: the firm's debt is cancelled but the bank asset is never
\* written down -- the one-sided write-off.  The shadow carries claims against
\* firms that no longer exist, overstating the loan book by exactly everything
\* ever written off.  Distinct from shadow one: that one mis-sizes the loss,
\* this one never realises it at all, and an implementation can have either
\* without the other.
OneSidedWriteOffKeepsClaim == shadowLoans = bankLoans + cumClaim

OneSidedWriteOffBreaksMirror ==
    cumClaim > 0 => (shadowLoans # Total(debt))

\* -- Action properties ---------------------------------------------------
\* The write-off is TWO-SIDED: the firm's debt and the bank's asset fall by the
\* same amount in the same step.  This is the property shadow two violates.
WriteOffIsTwoSided ==
    [][ (cumClaim' > cumClaim) =>
            /\ bankLoans'    = bankLoans - (cumClaim' - cumClaim)
            /\ Total(debt')  = Total(debt) - (cumClaim' - cumClaim) ]_vars

\* Capital absorbs the LOSS and only the loss -- never the recovered part.
CapitalAbsorbsLossOnly ==
    [][ (cumClaim' > cumClaim) =>
            (bankEquity' = bankEquity - (cumLoss' - cumLoss)) ]_vars

\* The deposit liability falls by exactly what was seized: the recovery is a
\* transfer of the firm's own money, not an injection.
SeizureDebitsDeposits ==
    [][ (cumClaim' > cumClaim) =>
            (bankDeposits' = bankDeposits - (cumRecovery' - cumRecovery)) ]_vars

\* No firm exits that the insolvency draw did not select.
NoExitWithoutDraw ==
    [][ (cumExits' > cumExits) => (cumDesired' > cumDesired) ]_vars

\* An exit is permanent -- a retired firm never comes back to be written off
\* a second time.
ExitsAreIrreversible ==
    [][ \A f \in Firms : ~alive[f] => ~alive'[f] ]_vars

\* Closure is preserved step by step, not merely at the endpoints.
ClosurePreservedStepwise ==
    [][ (bankLoans' + bankBonds') - (bankDeposits' + bankEquity')
          = (bankLoans + bankBonds) - (bankDeposits + bankEquity) ]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
