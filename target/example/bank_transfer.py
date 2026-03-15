"""
Example target: Bank account transfer with a deliberate concurrency bug.

BUG: transfer() reads both balances, then writes both. If two transfers
execute concurrently, they can read stale values and violate the
conservation invariant (total money in the system changes).

This is the classic TOCTOU (time-of-check-time-of-use) race condition.
TLC will find the exact interleaving that triggers it.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from threading import Thread


@dataclass
class Account:
    id: str
    balance: int = 0


@dataclass
class Bank:
    accounts: dict[str, Account] = field(default_factory=dict)

    def create_account(self, id: str, initial_balance: int) -> Account:
        acc = Account(id=id, balance=initial_balance)
        self.accounts[id] = acc
        return acc

    def transfer(self, from_id: str, to_id: str, amount: int) -> bool:
        """
        Transfer money between accounts.

        BUG: This is NOT atomic. Two concurrent transfers can interleave:
          T1: reads from_acc.balance = 100
          T2: reads from_acc.balance = 100
          T1: from_acc.balance = 100 - 50 = 50
          T2: from_acc.balance = 100 - 30 = 70   ← stale read!
          T1: to_acc.balance += 50
          T2: to_acc.balance += 30
          Result: money created from thin air (conservation violated)
        """
        from_acc = self.accounts.get(from_id)
        to_acc = self.accounts.get(to_id)

        if from_acc is None or to_acc is None:
            return False

        # Read (non-atomic with the write below)
        current_balance = from_acc.balance

        if current_balance < amount:
            return False

        # Write (may be based on stale read)
        from_acc.balance = current_balance - amount
        to_acc.balance = to_acc.balance + amount
        return True

    def total_balance(self) -> int:
        """Conservation invariant: total money should never change."""
        return sum(acc.balance for acc in self.accounts.values())


def demo_race_condition():
    """Demonstrate the race condition with threads."""
    bank = Bank()
    bank.create_account("alice", 100)
    bank.create_account("bob", 100)

    initial_total = bank.total_balance()  # Should always be 200

    threads = [
        Thread(target=bank.transfer, args=("alice", "bob", 50)),
        Thread(target=bank.transfer, args=("bob", "alice", 30)),
    ]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    final_total = bank.total_balance()
    if final_total != initial_total:
        print(f"BUG! Total changed: {initial_total} → {final_total}")
    else:
        print(f"OK (this time): total = {final_total}")


if __name__ == "__main__":
    # Race condition is non-deterministic — may need many runs to trigger
    for i in range(100):
        demo_race_condition()
