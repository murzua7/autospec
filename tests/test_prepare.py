"""Tests for the prepare.py evaluator (TLC harness)."""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

# Add project root to path
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from prepare import (
    TLCResult,
    TraceStep,
    Violation,
    evaluate_spec_quality,
    format_result_for_agent,
    format_result_tsv,
    parse_tlc_output,
    run_tlc,
    self_hash,
)


class TestSelfHash:
    def test_returns_hex_string(self):
        h = self_hash()
        assert isinstance(h, str)
        assert len(h) == 64  # SHA256 hex

    def test_consistent(self):
        assert self_hash() == self_hash()


class TestParseTLCOutput:
    def test_parse_successful_run(self):
        raw = """
TLC2 Version 2026.03.12
Starting... (2026-03-15 15:00:00)
Computing initial states...
Finished computing initial states: 10 distinct states generated.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
100 states generated, 50 distinct states found, 0 states left on queue.
Finished in 02s at (2026-03-15 15:00:02)
"""
        result = parse_tlc_output(raw, "test.tla", "test.cfg")
        assert result.states_found == 100
        assert result.distinct_states == 50
        assert result.violation_count == 0
        assert result.passed is True

    def test_parse_invariant_violation(self):
        raw = """
Starting... (2026-03-15 15:00:00)
Finished computing initial states: 5 distinct states generated.
Error: Invariant MoneyConserved is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\\ balance = (a1 :> 0 @@ a2 :> 1)
/\\ pc = (t1 :> "init")
State 2: <ReadBalance(t1) line 10>
/\\ balance = (a1 :> 0 @@ a2 :> 0)
/\\ pc = (t1 :> "read")
100 states generated, 80 distinct states found, 5 states left on queue.
Finished in 01s at (2026-03-15 15:00:01)
"""
        result = parse_tlc_output(raw, "test.tla", "test.cfg")
        assert result.violation_count == 1
        assert result.invariant_violations == 1
        assert result.violations[0].violation_type == "invariant"
        assert result.violations[0].property_name == "MoneyConserved"
        assert len(result.violations[0].trace) == 2
        assert result.violations[0].trace[0].step_number == 1
        assert "balance" in result.violations[0].trace[0].variables

    def test_parse_deadlock(self):
        raw = """
Starting... (2026-03-15 15:00:00)
Error: Deadlock reached.
50 states generated, 30 distinct states found, 0 states left on queue.
Finished in 01s
"""
        result = parse_tlc_output(raw, "test.tla", "test.cfg")
        assert result.deadlocks == 1
        assert result.violation_count == 1
        assert result.violations[0].violation_type == "deadlock"

    def test_parse_errors(self):
        raw = """
*** Errors: 1
Unknown operator: FooBar
"""
        result = parse_tlc_output(raw, "test.tla", "test.cfg")
        assert len(result.parse_errors) >= 1
        assert result.passed is False


class TestEvaluateSpecQuality:
    def test_basic_quality(self, tmp_path):
        spec = tmp_path / "test.tla"
        spec.write_text("""
---- MODULE test ----
VARIABLES x
TypeOK == x \\in Int
Safety == x >= 0
INVARIANT TypeOK
INVARIANT Safety
PROPERTY Liveness
====
""")
        result = TLCResult(
            spec_file=str(spec),
            config_file="test.cfg",
            passed=True,
            states_found=100,
            distinct_states=50,
            time_seconds=1.5,
        )
        q = evaluate_spec_quality(result, spec)
        assert q.violation_count == 0
        assert q.states_explored == 100
        assert q.passed is True


class TestFormatting:
    def test_format_result_for_agent(self):
        result = TLCResult(
            spec_file="test.tla",
            config_file="test.cfg",
            passed=False,
            violation_count=1,
            invariant_violations=1,
            states_found=100,
            distinct_states=50,
            time_seconds=1.5,
            violations=[
                Violation(
                    violation_type="invariant",
                    property_name="Safety",
                    trace=[
                        TraceStep(1, "Initial predicate", {"x": "0"}),
                        TraceStep(2, "Action1", {"x": "-1"}),
                    ],
                )
            ],
        )
        text = format_result_for_agent(result)
        assert "VIOLATION 1" in text
        assert "Safety" in text
        assert "State 1" in text
        assert "State 2" in text

    def test_format_result_tsv(self):
        result = TLCResult(
            spec_file="test.tla",
            config_file="test.cfg",
            violation_count=2,
            invariant_violations=1,
            deadlocks=1,
            states_found=100,
            distinct_states=50,
            time_seconds=1.5,
        )
        line = format_result_tsv(1, result, "KEEP", "test summary")
        fields = line.split("\t")
        assert fields[0] == "1"
        assert fields[1] == "KEEP"
        assert fields[2] == "2"  # violations


class TestRunTLC:
    """Integration tests that run actual TLC on the example spec."""

    @pytest.fixture
    def specs_dir(self):
        return ROOT / "specs"

    def test_bank_transfer_finds_violation(self, specs_dir):
        """TLC should find MoneyConserved violation in BankTransfer spec."""
        spec = specs_dir / "BankTransfer.tla"
        cfg = specs_dir / "BankTransfer.cfg"
        if not spec.exists() or not cfg.exists():
            pytest.skip("BankTransfer spec not found")

        result = run_tlc(spec, cfg, timeout=60)
        assert result.violation_count >= 1
        assert result.invariant_violations >= 1
        # Should find MoneyConserved violation
        names = [v.property_name for v in result.violations]
        assert "MoneyConserved" in names
        # Should have a counterexample trace
        for v in result.violations:
            if v.property_name == "MoneyConserved":
                assert len(v.trace) >= 2

    def test_missing_spec(self):
        result = run_tlc("nonexistent.tla")
        assert not result.passed
        assert "not found" in result.error_message
