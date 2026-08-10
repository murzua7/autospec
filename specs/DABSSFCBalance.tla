---- MODULE DABSSFCBalance ----
\* SFC-1: whole-economy stock-flow consistency in _phase_balance_sheets.
\*
\* Target: dabs/approaches/batched/simulation.py:2841 _phase_balance_sheets,
\* the phase that posts the quarter's financial flows onto the sector and bank
\* balance sheets.  Mechanism, as transcribed from the code at e6daf7c: every
\* financial flow is a PAIRED double-entry posting, so bank deposits equal the
\* sum of sector deposit holdings, outstanding loans mirror the sum of sector
\* debts, and the bank balance sheet loans + bonds = deposits + equity closes
\* in every reachable state.
\*
\* The one modelling decision that makes this non-vacuous: bankEquity is an
\* INDEPENDENT state variable, moved only by the postings that touch it --
\* interest booked to capital, write-offs absorbed by capital.  Recomputing it
\* as assets minus liabilities would turn the closure invariant into an
\* identity that no coding error could break.  Likewise bankDeposits and
\* bankLoans are the BANK's own ledgers, advanced by the bank leg of each
\* posting, while deposits[] and debts[] are the SECTOR ledgers advanced by the
\* sector leg.  Neither side is derived from the other, so a posting that
\* updates one leg and forgets its counterparty is exactly what the mirror
\* invariants below catch.
\*
\* Scope note: the narrower endogenous-money identity (MONEY-1) is deliberately
\* NOT asserted here.  InterestToCapital and WriteOff move deposits and loans
\* outside the lend/repay pair, so that identity holds only over the subset of
\* postings MONEY-1 will model.  Closure below holds over ALL of them.
\*
\* The falsifiable bite is sloppyDeposits: a shadow bank deposit ledger that
\* posts the CREDIT leg of a settlement and forgets the DEBIT leg.  That is the
\* one-sided posting tensor code actually produces -- a scatter-add lands on the
\* receiver index and the sender index is never decremented.  Every property of
\* the real ledger is stated alongside the shadow one, so the spec pins both the
\* correct behaviour and the shape of the failure.

EXTENDS Integers

CONSTANTS
    NumSectors,     \* sector ledgers: firms, households, government
    MaxSteps,       \* rollout length
    MaxAmount,      \* bound on one posting
    InitEquity      \* opening bank capital, held against government bonds

ASSUME /\ NumSectors \in Nat /\ NumSectors > 1
       /\ MaxSteps   \in Nat
       /\ MaxAmount  \in Nat /\ MaxAmount > 0
       /\ InitEquity \in Nat

Sectors == 1..NumSectors
Gov     == NumSectors    \* the sector the bond proceeds are credited to

VARIABLES
    t,              \* step counter (the quarterly clock)
    deposits,       \* SECTOR ledger: each sector's deposit holding
    debts,          \* SECTOR ledger: each sector's outstanding loan
    bankDeposits,   \* BANK ledger: deposit liability, posted independently
    bankLoans,      \* BANK ledger: loan asset, posted independently
    bankBonds,      \* BANK ledger: government bonds held
    bankEquity,     \* BANK capital, an INDEPENDENT variable, never recomputed
    govBonds,       \* government bonds issued
    cumLent,        \* cumulative lending flow
    cumRepaid,      \* cumulative repayment flow
    cumWritten,     \* cumulative written-off principal
    cumTransferred, \* cumulative settlement volume
    sloppyDeposits  \* shadow ledger with the DEBIT leg of settlement dropped

vars == <<t, deposits, debts, bankDeposits, bankLoans, bankBonds, bankEquity,
          govBonds, cumLent, cumRepaid, cumWritten, cumTransferred,
          sloppyDeposits>>

Sum(f, S) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN  f[x] + g[T \ {x}]
             IN  g[S]

Total(f) == Sum(f, Sectors)

Amounts  == 1..MaxAmount
Flow     == MaxAmount * MaxSteps
MaxStock == InitEquity + Flow
Stocks   == 0..MaxStock
Flows    == 0..Flow

\* -- Type invariant ------------------------------------------------------
TypeOK ==
    /\ t              \in 0..MaxSteps
    /\ deposits       \in [Sectors -> Flows]
    /\ debts          \in [Sectors -> Flows]
    /\ bankDeposits   \in Flows
    /\ bankLoans      \in Flows
    /\ bankBonds      \in Stocks
    /\ bankEquity     \in (0 - Flow)..MaxStock
    /\ govBonds       \in Stocks
    /\ cumLent        \in Flows
    /\ cumRepaid      \in Flows
    /\ cumWritten     \in Flows
    /\ cumTransferred \in Flows
    /\ sloppyDeposits \in Flows

\* -- Initial state -------------------------------------------------------
\* The economy opens with no credit and no deposits; the bank's capital is held
\* against government bonds, so the opening balance sheet already closes with a
\* non-zero asset side.
Init ==
    /\ t              = 0
    /\ deposits       = [s \in Sectors |-> 0]
    /\ debts          = [s \in Sectors |-> 0]
    /\ bankDeposits   = 0
    /\ bankLoans      = 0
    /\ bankBonds      = InitEquity
    /\ bankEquity     = InitEquity
    /\ govBonds       = InitEquity
    /\ cumLent        = 0
    /\ cumRepaid      = 0
    /\ cumWritten     = 0
    /\ cumTransferred = 0
    /\ sloppyDeposits = 0

\* -- Postings ------------------------------------------------------------
\* Each action is ONE double-entry posting.  Both legs are written explicitly;
\* neither is inferred from the other.

\* Bank lends: loan asset up, deposit liability up, sector debt and sector
\* deposit up.  This is where money is created.
Lend(s, amt) ==
    /\ deposits'       = [deposits EXCEPT ![s] = @ + amt]
    /\ debts'          = [debts    EXCEPT ![s] = @ + amt]
    /\ bankDeposits'   = bankDeposits + amt
    /\ bankLoans'      = bankLoans + amt
    /\ sloppyDeposits' = sloppyDeposits + amt
    /\ cumLent'        = cumLent + amt
    /\ UNCHANGED <<bankBonds, bankEquity, govBonds, cumRepaid, cumWritten,
                   cumTransferred>>

\* Repayment: the mirror posting.  Money is destroyed.
Repay(s, amt) ==
    /\ debts[s]    >= amt
    /\ deposits[s] >= amt
    /\ deposits'       = [deposits EXCEPT ![s] = @ - amt]
    /\ debts'          = [debts    EXCEPT ![s] = @ - amt]
    /\ bankDeposits'   = bankDeposits - amt
    /\ bankLoans'      = bankLoans - amt
    /\ sloppyDeposits' = sloppyDeposits - amt
    /\ cumRepaid'      = cumRepaid + amt
    /\ UNCHANGED <<bankBonds, bankEquity, govBonds, cumLent, cumWritten,
                   cumTransferred>>

\* Goods settlement or a transfer: deposits RELOCATE between sectors.  The
\* bank's deposit liability is untouched -- nothing is created or destroyed.
\* sloppyDeposits posts the credit and drops the debit: the defect.
Settle(from, to, amt) ==
    /\ from # to
    /\ deposits[from] >= amt
    /\ deposits'       = [deposits EXCEPT ![from] = @ - amt, ![to] = @ + amt]
    /\ sloppyDeposits' = sloppyDeposits + amt
    /\ cumTransferred' = cumTransferred + amt
    /\ UNCHANGED <<debts, bankDeposits, bankLoans, bankBonds, bankEquity,
                   govBonds, cumLent, cumRepaid, cumWritten>>

\* Interest income booked to capital: the sector's deposit is debited and the
\* bank's capital is credited.  Equity moves because a POSTING moved it.
InterestToCapital(s, amt) ==
    /\ deposits[s] >= amt
    /\ deposits'       = [deposits EXCEPT ![s] = @ - amt]
    /\ bankDeposits'   = bankDeposits - amt
    /\ bankEquity'     = bankEquity + amt
    /\ sloppyDeposits' = sloppyDeposits - amt
    /\ UNCHANGED <<debts, bankLoans, bankBonds, govBonds, cumLent, cumRepaid,
                   cumWritten, cumTransferred>>

\* Bank buys newly issued government debt: bond asset up, government deposit up.
BuyBond(amt) ==
    /\ deposits'       = [deposits EXCEPT ![Gov] = @ + amt]
    /\ bankDeposits'   = bankDeposits + amt
    /\ bankBonds'      = bankBonds + amt
    /\ govBonds'       = govBonds + amt
    /\ sloppyDeposits' = sloppyDeposits + amt
    /\ UNCHANGED <<debts, bankLoans, bankEquity, cumLent, cumRepaid,
                   cumWritten, cumTransferred>>

\* Loan write-off: the firm's debt disappears AND the bank's asset is written
\* down, with capital absorbing the loss.  Both sides move together.
WriteOff(s, amt) ==
    /\ debts[s] >= amt
    /\ debts'      = [debts EXCEPT ![s] = @ - amt]
    /\ bankLoans'  = bankLoans - amt
    /\ bankEquity' = bankEquity - amt
    /\ cumWritten' = cumWritten + amt
    /\ UNCHANGED <<deposits, bankDeposits, bankBonds, govBonds, cumLent,
                   cumRepaid, cumTransferred, sloppyDeposits>>

Done == /\ t = MaxSteps
        /\ UNCHANGED vars

Next ==
    \/ /\ t < MaxSteps
       /\ t' = t + 1
       /\ \/ \E s \in Sectors, a \in Amounts : Lend(s, a)
          \/ \E s \in Sectors, a \in Amounts : Repay(s, a)
          \/ \E p, q \in Sectors, a \in Amounts : Settle(p, q, a)
          \/ \E s \in Sectors, a \in Amounts : InterestToCapital(s, a)
          \/ \E a \in Amounts : BuyBond(a)
          \/ \E s \in Sectors, a \in Amounts : WriteOff(s, a)
    \/ Done

\* -- Safety invariants ---------------------------------------------------

\* The two mirror identities.  These are what fail if a posting writes the bank
\* leg and forgets the sector leg, or scatters onto the wrong agent index, or
\* applies a per-sector update with a broadcast that hits every sector.
DepositLedgerMirrors == bankDeposits = Total(deposits)
LoanLedgerMirrors    == bankLoans    = Total(debts)

\* The bank balance sheet closes in every reachable state.  Non-vacuous because
\* bankEquity is posted, not recomputed: any posting that moves one side without
\* its counterparty breaks this immediately.
BalanceSheetCloses == bankLoans + bankBonds = bankDeposits + bankEquity

\* Bonds held equal bonds issued -- the bank is the sole holder in this model.
BondsMatchIssuance == bankBonds = govBonds

\* No sector holds a negative deposit or a negative debt.  Fails if settlement
\* were allowed to overdraw, i.e. if the precondition on the debit leg were
\* dropped in favour of an unfloored subtraction.
DepositsNonNegative == \A s \in Sectors : deposits[s] >= 0
DebtsNonNegative    == \A s \in Sectors : debts[s]    >= 0

\* The loan stock is exactly the integral of its three flows.  Because the
\* counters accumulate independently of the stock, a write-off that reduced the
\* bank asset without cancelling the firm's debt -- or cancelled the debt twice
\* -- breaks this identity while both mirrors above could still look healthy.
LoanStockFromFlows == bankLoans = cumLent - cumRepaid - cumWritten

\* -- the falsifiable bite -------------------------------------------------
\* The one-sided settlement posting overcounts by EXACTLY the volume settled.
SloppyLeakIsExactlyTransfers == sloppyDeposits = bankDeposits + cumTransferred

\* The leak is one-sided and UPWARD: a dropped debit can only inflate the
\* liability side, never deflate it.
SloppyOvercounts == sloppyDeposits >= bankDeposits

\* And the consequence: once any settlement has happened, the bank balance
\* sheet built on the sloppy ledger no longer closes.  This is the state in
\* which the economy is silently creating money out of goods trade.
SloppyBreaksClosure ==
    cumTransferred > 0 =>
        (bankLoans + bankBonds # sloppyDeposits + bankEquity)

\* -- Action properties ---------------------------------------------------
\* Settlement RELOCATES deposits and never creates them.  This is the property
\* that separates a transfer from an issuance, and it is what a phase ordering
\* fault would break by settling through the lending path.
SettlementIsNeutral ==
    [][ (cumTransferred' > cumTransferred) => (bankDeposits' = bankDeposits) ]_vars

\* Lending creates deposits one for one with the loan booked.
LendingCreatesDeposits ==
    [][ (cumLent' > cumLent) =>
            (bankDeposits' = bankDeposits + (cumLent' - cumLent)) ]_vars

\* A write-off is absorbed by capital, unit for unit -- never by depositors.
WriteOffHitsCapital ==
    [][ (cumWritten' > cumWritten) =>
            (bankEquity' = bankEquity - (cumWritten' - cumWritten)) ]_vars

\* -- Specification -------------------------------------------------------
Spec == Init /\ [][Next]_vars

====
