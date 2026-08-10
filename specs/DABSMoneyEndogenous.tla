---- MODULE DABSMoneyEndogenous ----
\* MONEY-1: endogenous money creation and destruction.
\*
\* Target: dabs/approaches/batched/simulation.py:2015 _phase_credit, together
\* with dabs/markets/credit.py:27.  Mechanism, as transcribed from the code at
\* e6daf7c: the deposit stock changes ONLY via bank lending (creation) and
\* repayment (destruction).  Goods settlement, wage payment, tax and transfers
\* RELOCATE deposits between sectors without creating or destroying any, so
\* total_deposits - outstanding_loans is a constant of the motion in every
\* reachable state.
\*
\* Why this is NOT already covered by DABSSFCBalance (SFC-1).  That spec asserts
\* the bank's balance-sheet CLOSURE, loans + bonds = deposits + equity, and its
\* own scope note explicitly declines the endogenous-money identity because
\* interest and write-offs move deposits and loans outside the lend/repay pair.
\* Closure is an accounting identity over ALL postings; endogenous money is a
\* PARTITION claim about which postings may move the aggregate at all.  A model
\* can close its balance sheet perfectly while creating money out of goods
\* trade -- book the settlement as a fresh drawdown and credit the equity side
\* to match, and closure survives while the money stock inflates.  That is the
\* defect this spec exists to catch, and SFC-1 cannot see it.
\*
\* The modelling decision that makes this non-vacuous: bankDeposits is an
\* INDEPENDENT variable advanced by each posting's own deposit leg.  Deriving it
\* as bankLoans + Base would make the headline identity a tautology no coding
\* error could break.  Likewise every posting carries an explicit class tag --
\* CREATE, DESTROY or NEUTRAL -- assigned by which code path books it, and the
\* action properties below check the aggregate against that tag.  A posting that
\* claims to be neutral and moves the aggregate is exactly the failure.
\*
\* Interest and write-offs, which SFC-1 models, are deliberately EXCLUDED here.
\* They are the postings that legitimately break this narrower identity, and
\* including them would force the invariant to be weakened into uselessness.
\* The two specs together cover the whole posting set: this one pins the
\* monetary partition over the lend/repay/settle core, SFC-1 pins closure over
\* everything.

EXTENDS Integers

CONSTANTS
    NumSectors,     \* sector deposit ledgers: firms, households, government
    MaxSteps,       \* rollout length
    MaxAmount,      \* bound on one posting
    Base            \* opening outside money: deposits held against no bank loan

ASSUME /\ NumSectors \in Nat /\ NumSectors > 1
       /\ MaxSteps   \in Nat
       /\ MaxAmount  \in Nat /\ MaxAmount > 0
       /\ Base       \in Nat /\ Base > 0

Sectors == 1..NumSectors

VARIABLES
    t,              \* step counter (the quarterly clock)
    deposits,       \* SECTOR ledger: each sector's deposit holding
    debts,          \* SECTOR ledger: each sector's outstanding loan
    bankDeposits,   \* BANK ledger: the money stock, posted INDEPENDENTLY
    bankLoans,      \* BANK ledger: the loan asset, posted INDEPENDENTLY
    cumCreated,     \* cumulative money created by lending
    cumDestroyed,   \* cumulative money destroyed by repayment
    cumRelocated,   \* cumulative volume moved by NEUTRAL postings
    lastClass,      \* class of the posting just made: 0 none, 1 create,
                    \* 2 destroy, 3 neutral
    creditRouted,   \* shadow: settlement booked through the CREDIT path
    lossyRepay      \* shadow: repayment that cancels the loan, keeps the money

vars == <<t, deposits, debts, bankDeposits, bankLoans, cumCreated,
          cumDestroyed, cumRelocated, lastClass, creditRouted, lossyRepay>>

Sum(f, S) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN  f[x] + g[T \ {x}]
             IN  g[S]

Total(f) == Sum(f, Sectors)

Amounts  == 1..MaxAmount
Flow     == MaxAmount * MaxSteps
MaxStock == Base + Flow
Stocks   == 0..MaxStock
Flows    == 0..Flow

\* Posting classes, named so the action properties read as the code does.
NoPosting == 0
Create    == 1
Destroy   == 2
Neutral   == 3

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t            \in 0..MaxSteps
    /\ deposits     \in [Sectors -> Stocks]
    /\ debts        \in [Sectors -> Flows]
    /\ bankDeposits \in Stocks
    /\ bankLoans    \in Flows
    /\ cumCreated   \in Flows
    /\ cumDestroyed \in Flows
    /\ cumRelocated \in Flows
    /\ lastClass    \in {NoPosting, Create, Destroy, Neutral}
    /\ creditRouted \in Stocks
    /\ lossyRepay   \in Stocks

\* -- Initial state -------------------------------------------------------
\* The economy opens with Base units of outside money, all held by the first
\* sector, and no credit outstanding.  A strictly positive Base is what makes
\* the neutral postings genuinely enabled from the first step: with an empty
\* opening ledger nothing could be settled until something had been lent, and
\* the relocation invariants would be reachable only through the credit path.
Init ==
    /\ t            = 0
    /\ deposits     = [s \in Sectors |-> IF s = 1 THEN Base ELSE 0]
    /\ debts        = [s \in Sectors |-> 0]
    /\ bankDeposits = Base
    /\ bankLoans    = 0
    /\ cumCreated   = 0
    /\ cumDestroyed = 0
    /\ cumRelocated = 0
    /\ lastClass    = NoPosting
    /\ creditRouted = Base
    /\ lossyRepay   = Base

\* -- Postings ------------------------------------------------------------
\* CREATE.  The bank lends: the loan asset and the deposit liability appear
\* together, out of nothing.  This is the ONLY path by which the aggregate may
\* rise.  Both the bank leg and the sector leg are written explicitly.
Lend(s, amt) ==
    /\ deposits'     = [deposits EXCEPT ![s] = @ + amt]
    /\ debts'        = [debts    EXCEPT ![s] = @ + amt]
    /\ bankDeposits' = bankDeposits + amt
    /\ bankLoans'    = bankLoans + amt
    /\ cumCreated'   = cumCreated + amt
    /\ lastClass'    = Create
    /\ creditRouted' = creditRouted + amt
    /\ lossyRepay'   = lossyRepay + amt
    /\ UNCHANGED <<cumDestroyed, cumRelocated>>

\* DESTROY.  Repayment: the borrower's deposit is extinguished against the
\* loan.  The ONLY path by which the aggregate may fall.  lossyRepay is the
\* shadow that cancels the debt and forgets to debit the deposit.
Repay(s, amt) ==
    /\ debts[s]    >= amt
    /\ deposits[s] >= amt
    /\ deposits'     = [deposits EXCEPT ![s] = @ - amt]
    /\ debts'        = [debts    EXCEPT ![s] = @ - amt]
    /\ bankDeposits' = bankDeposits - amt
    /\ bankLoans'    = bankLoans - amt
    /\ cumDestroyed' = cumDestroyed + amt
    /\ lastClass'    = Destroy
    /\ creditRouted' = creditRouted - amt
    /\ lossyRepay'   = lossyRepay
    /\ UNCHANGED <<cumCreated, cumRelocated>>

\* NEUTRAL.  Goods settlement, a wage payment, a tax remittance, a transfer:
\* deposits move BETWEEN sectors and the aggregate is untouched.  creditRouted
\* is the shadow in which this same flow is booked through the credit path --
\* a fresh drawdown credited to the receiver, the sender never debited at the
\* bank -- which is the phase-ordering fault MONEY-1 exists to catch.
Settle(from, to, amt) ==
    /\ from # to
    /\ deposits[from] >= amt
    /\ deposits'     = [deposits EXCEPT ![from] = @ - amt, ![to] = @ + amt]
    /\ bankDeposits' = bankDeposits
    /\ cumRelocated' = cumRelocated + amt
    /\ lastClass'    = Neutral
    /\ creditRouted' = creditRouted + amt
    /\ lossyRepay'   = lossyRepay
    /\ UNCHANGED <<debts, bankLoans, cumCreated, cumDestroyed>>

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ /\ t < MaxSteps
       /\ t' = t + 1
       /\ \/ \E s \in Sectors, a \in Amounts : Lend(s, a)
          \/ \E s \in Sectors, a \in Amounts : Repay(s, a)
          \/ \E p, q \in Sectors, a \in Amounts : Settle(p, q, a)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* THE headline property: the money stock net of credit is a constant of the
\* motion.  Non-vacuous because bankDeposits and bankLoans are posted
\* independently by every action -- nothing here is recomputed from anything
\* else.  This fails the instant a settlement is routed through the lending
\* path, or a transfer credits the receiver without debiting the sender.
EndogenousMoneyIdentity == bankDeposits - bankLoans = Base

\* The bank's aggregate matches the sum of what the sectors actually hold.
\* A one-sided scatter-add onto the receiver index breaks this while the
\* identity above could still look healthy if the bank leg were left alone.
DepositLedgerMirrors == bankDeposits = Total(deposits)
LoanLedgerMirrors    == bankLoans    = Total(debts)

\* The money stock reconstructs exactly from its two permitted flows.  Because
\* the counters accumulate independently of the stock, a posting that moved the
\* aggregate without being classified -- the whole failure mode -- shows up here
\* even if the sector ledgers happened to stay consistent.
StockFromFlows == bankDeposits = Base + cumCreated - cumDestroyed

\* Relocation never enters the money stock.  cumRelocated can be arbitrarily
\* large while the aggregate is unmoved: that is precisely the claim.
RelocationIsNotCreation ==
    bankDeposits = Base + cumCreated - cumDestroyed

\* No sector holds a negative deposit or a negative debt.  Fails if settlement
\* were allowed to overdraw, i.e. if the precondition on the debit leg were
\* replaced by an unfloored subtraction -- the smooth_min escape of SMOOTH-1
\* landing on a ledger.
DepositsNonNegative == \A s \in Sectors : deposits[s] >= 0
DebtsNonNegative    == \A s \in Sectors : debts[s]    >= 0

\* Money can never be destroyed below the outside-money base: repayment is
\* bounded by what lending created.  Fails if a repayment path could run
\* against a loan that was never booked.
DestructionBoundedByCreation == cumDestroyed =< cumCreated

\* Outstanding credit is exactly the integral of its two flows.
CreditFromFlows == bankLoans = cumCreated - cumDestroyed

\* -- the falsifiable bite -------------------------------------------------
\* Shadow one: goods settlement routed through the credit path.  The money
\* stock is inflated by EXACTLY the volume settled -- every trade in the
\* economy prints money.  This is what a phase ordering that books the goods
\* settlement as a drawdown instead of a transfer actually does.
CreditRoutedInflatesByTradeVolume ==
    creditRouted = bankDeposits + cumRelocated

\* The inflation is one-sided and UPWARD: a settlement mis-booked as credit can
\* only print, never burn.
CreditRoutedOvercounts == creditRouted >= bankDeposits

\* And the consequence: once any trade has settled, the endogenous-money
\* identity fails on the shadow ledger.  This is the state in which the model
\* is silently monetising goods trade.
CreditRoutedBreaksIdentity ==
    cumRelocated > 0 => (creditRouted - bankLoans # Base)

\* Shadow two: repayment cancels the debt but never debits the deposit -- the
\* one-sided destruction.  Money stays outstanding against an asset that no
\* longer exists, so the shadow overstates the stock by exactly everything ever
\* repaid.  Distinct from shadow one: that one prints on trade, this one fails
\* to burn on repayment, and a real implementation can have either without the
\* other.
LossyRepayKeepsDestroyedMoney ==
    lossyRepay = bankDeposits + cumDestroyed

LossyRepayBreaksIdentity ==
    cumDestroyed > 0 => (lossyRepay - bankLoans # Base)

\* -- Action properties ---------------------------------------------------
\* The partition claim, stated directly on the transitions.  Each posting is
\* tagged by the code path that books it, and the aggregate must move exactly
\* as that tag permits.  These are what fail if a phase is reordered so that a
\* settlement runs through _phase_credit.

\* A NEUTRAL posting leaves the money stock EXACTLY unchanged.  Not bounded,
\* not approximately: unchanged.
NeutralPostingsDoNotMoveMoney ==
    [][ (lastClass' = Neutral) => (bankDeposits' = bankDeposits) ]_vars

\* ... while genuinely relocating deposits, so the property above is not
\* holding because nothing happened.
NeutralPostingsDoRelocate ==
    [][ (lastClass' = Neutral) => (cumRelocated' > cumRelocated) ]_vars

\* Creation moves deposits and loans one for one, together.
CreationIsPaired ==
    [][ (lastClass' = Create) =>
            /\ bankDeposits' = bankDeposits + (cumCreated' - cumCreated)
            /\ bankLoans'    = bankLoans    + (cumCreated' - cumCreated) ]_vars

\* Destruction likewise, in the other direction.
DestructionIsPaired ==
    [][ (lastClass' = Destroy) =>
            /\ bankDeposits' = bankDeposits - (cumDestroyed' - cumDestroyed)
            /\ bankLoans'    = bankLoans    - (cumDestroyed' - cumDestroyed) ]_vars

\* The money stock moves ONLY when a credit posting is booked.  The contrapositive
\* of the partition: no third path exists.
MoneyMovesOnlyOnCredit ==
    [][ (bankDeposits' # bankDeposits) =>
            (lastClass' \in {Create, Destroy}) ]_vars

\* Credit stock and money stock move in lockstep, always, so the identity is
\* preserved step by step and not merely at the endpoints.
IdentityPreservedStepwise ==
    [][ (bankDeposits' - bankLoans') = (bankDeposits - bankLoans) ]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
