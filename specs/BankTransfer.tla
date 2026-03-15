---- MODULE BankTransfer ----
\* TLA+ specification for the bank transfer system.
\* Models the concurrency bug in target/example/bank_transfer.py
\*
\* The code does:  read balance → check → write new balance
\* This is non-atomic, so concurrent transfers can interleave
\* between read and write, causing stale-read bugs.

EXTENDS Integers, TLC, FiniteSets

CONSTANTS
    Accounts,       \* Set of account IDs (model values)
    MaxBalance,     \* Upper bound for initial balances
    Transfers       \* Set of transfer IDs (concurrent transfer processes)

VARIABLES
    balance,        \* balance[a] = current balance of account a
    pc,             \* pc[t] = program counter for transfer t
    from_acc,       \* from_acc[t] = source account for transfer t
    to_acc,         \* to_acc[t] = destination account for transfer t
    amount,         \* amount[t] = transfer amount
    read_balance,   \* read_balance[t] = balance read in the non-atomic read step
    init_total      \* The total money at Init — should be conserved forever

vars == <<balance, pc, from_acc, to_acc, amount, read_balance, init_total>>

\* Helper: sum of all account balances
RECURSIVE SumBalances(_,_)
SumBalances(accs, bal) ==
    IF accs = {} THEN 0
    ELSE LET a == CHOOSE x \in accs: TRUE
         IN bal[a] + SumBalances(accs \ {a}, bal)

TotalMoney == SumBalances(Accounts, balance)

\* ── Type Invariant ────────────────────────────────────────────────────
\* Use Int (not bounded) so TypeOK doesn't mask the real conservation bug
TypeOK ==
    /\ balance \in [Accounts -> Int]
    /\ pc \in [Transfers -> {"init", "read", "check", "write_from", "write_to", "done", "failed"}]
    /\ from_acc \in [Transfers -> Accounts]
    /\ to_acc \in [Transfers -> Accounts]
    /\ amount \in [Transfers -> 1..MaxBalance]
    /\ read_balance \in [Transfers -> Int]
    /\ init_total \in Int

\* ── Initial State ─────────────────────────────────────────────────────
Init ==
    /\ balance \in [Accounts -> 0..MaxBalance]
    /\ pc = [t \in Transfers |-> "init"]
    /\ from_acc \in [Transfers -> Accounts]
    /\ to_acc \in [Transfers -> Accounts]
    /\ amount \in [Transfers -> 1..MaxBalance]
    /\ read_balance = [t \in Transfers |-> 0]
    /\ init_total = SumBalances(Accounts, balance)

\* ── Actions ───────────────────────────────────────────────────────────

StartTransfer(t) ==
    /\ pc[t] = "init"
    /\ from_acc[t] # to_acc[t]
    /\ pc' = [pc EXCEPT ![t] = "read"]
    /\ UNCHANGED <<balance, from_acc, to_acc, amount, read_balance, init_total>>

\* NON-ATOMIC READ: this is where the bug lives.
\* Another transfer can change the balance between this read and the write.
ReadBalance(t) ==
    /\ pc[t] = "read"
    /\ read_balance' = [read_balance EXCEPT ![t] = balance[from_acc[t]]]
    /\ pc' = [pc EXCEPT ![t] = "check"]
    /\ UNCHANGED <<balance, from_acc, to_acc, amount, init_total>>

CheckFunds(t) ==
    /\ pc[t] = "check"
    /\ IF read_balance[t] >= amount[t]
       THEN pc' = [pc EXCEPT ![t] = "write_from"]
       ELSE pc' = [pc EXCEPT ![t] = "failed"]
    /\ UNCHANGED <<balance, from_acc, to_acc, amount, read_balance, init_total>>

\* Write: debit source (using potentially STALE read_balance)
WriteFrom(t) ==
    /\ pc[t] = "write_from"
    /\ balance' = [balance EXCEPT ![from_acc[t]] = read_balance[t] - amount[t]]
    /\ pc' = [pc EXCEPT ![t] = "write_to"]
    /\ UNCHANGED <<from_acc, to_acc, amount, read_balance, init_total>>

\* Write: credit destination
WriteTo(t) ==
    /\ pc[t] = "write_to"
    /\ balance' = [balance EXCEPT ![to_acc[t]] = balance[to_acc[t]] + amount[t]]
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<from_acc, to_acc, amount, read_balance, init_total>>

\* ── Next-State Relation ───────────────────────────────────────────────
Next ==
    \E t \in Transfers:
        \/ StartTransfer(t)
        \/ ReadBalance(t)
        \/ CheckFunds(t)
        \/ WriteFrom(t)
        \/ WriteTo(t)

\* ── Specification ─────────────────────────────────────────────────────
Spec == Init /\ [][Next]_vars

\* ── SAFETY INVARIANTS ─────────────────────────────────────────────────

\* CONSERVATION: total money must equal initial total.
\* TLC WILL FIND a violation — two concurrent transfers reading the same
\* account will use stale balances, causing money creation/destruction.
MoneyConserved == TotalMoney = init_total

\* No balance should go negative (overdraft via stale read)
NoNegativeBalance == \A a \in Accounts: balance[a] >= 0

====
