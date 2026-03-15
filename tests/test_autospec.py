"""Tests for autospec.py orchestrator — security, accept/reject gate, parsing."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from autospec import (
    _NO_BASELINE,
    _parse_agent_response,
    apply_changes,
    load_current_specs,
)


class TestApplyChanges:
    """Security tests for the file-writing sandbox."""

    def test_allows_spec_files(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        (tmp_path / "specs").mkdir()
        output = {"files": {"specs/Test.tla": "---- MODULE Test ----\n===="}}
        written = apply_changes(output)
        assert "specs/Test.tla" in written
        assert (tmp_path / "specs" / "Test.tla").exists()

    def test_allows_target_files(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        (tmp_path / "target").mkdir()
        output = {"files": {"target/fix.py": "# fixed code"}}
        written = apply_changes(output)
        assert "target/fix.py" in written

    def test_blocks_prepare_py(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"prepare.py": "# hacked!"}}
        written = apply_changes(output)
        assert len(written) == 0
        assert not (tmp_path / "prepare.py").exists()

    def test_blocks_autospec_py(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"autospec.py": "# hacked!"}}
        written = apply_changes(output)
        assert len(written) == 0

    def test_blocks_program_md(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"program.md": "# new instructions"}}
        written = apply_changes(output)
        assert len(written) == 0

    def test_blocks_path_traversal(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"../../etc/passwd": "hacked"}}
        written = apply_changes(output)
        assert len(written) == 0

    def test_blocks_path_traversal_in_allowed_prefix(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"specs/../../escape.txt": "hacked"}}
        written = apply_changes(output)
        assert len(written) == 0

    def test_blocks_root_level_files(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        output = {"files": {"evil.py": "import os; os.system('rm -rf /')"}}
        written = apply_changes(output)
        assert len(written) == 0

    def test_blocks_pyproject(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.ROOT", tmp_path)
        (tmp_path / "specs").mkdir()
        # pyproject.toml is in FORBIDDEN_NAMES, so blocked everywhere
        output = {"files": {"pyproject.toml": "bad"}}
        written = apply_changes(output)
        assert "pyproject.toml" not in written
        # But a .tla file in specs/ is allowed
        output2 = {"files": {"specs/Test.tla": "ok"}}
        written2 = apply_changes(output2)
        assert "specs/Test.tla" in written2


class TestParseAgentResponse:
    def test_parse_json_in_code_fence(self):
        text = '''Here is my response:
```json
{"summary": "test", "classification": "NEW_SPEC", "files": {}, "reasoning": "ok", "next_focus": "", "focus_module": ""}
```'''
        result = _parse_agent_response(text)
        assert result["summary"] == "test"
        assert result["classification"] == "NEW_SPEC"

    def test_parse_raw_json(self):
        text = '{"summary": "raw", "files": {}}'
        result = _parse_agent_response(text)
        assert result["summary"] == "raw"

    def test_parse_json_with_surrounding_text(self):
        text = 'Let me analyze the code. {"summary": "found bug", "files": {"specs/A.tla": "content"}} That should fix it.'
        result = _parse_agent_response(text)
        assert result["summary"] == "found bug"
        assert "specs/A.tla" in result["files"]

    def test_unparseable_returns_error(self):
        text = "This has absolutely plain text only."
        result = _parse_agent_response(text)
        assert result["classification"] == "ERROR"
        # The raw text is preserved in reasoning for debugging
        assert "plain text" in result["reasoning"]

    def test_handles_empty_string(self):
        result = _parse_agent_response("")
        assert result["classification"] == "ERROR"

    def test_handles_json_in_code_fence_with_braces_outside(self):
        # The code fence JSON parser should work even with braces in surrounding text
        text = '''I see the set in the spec. Here is my change:
```json
{"summary": "added invariant", "files": {"specs/Test.tla": "TypeOK"}}
```'''
        result = _parse_agent_response(text)
        assert result["summary"] == "added invariant"


class TestAcceptRejectConstants:
    def test_no_baseline_is_negative(self):
        """_NO_BASELINE must be negative so it's always < any real violation count."""
        assert _NO_BASELINE < 0

    def test_no_baseline_less_than_zero(self):
        """Any violation count (including 0) should be > _NO_BASELINE."""
        assert 0 > _NO_BASELINE
        assert 1 > _NO_BASELINE
        assert 100 > _NO_BASELINE


class TestLoadCurrentSpecs:
    def test_excludes_ttrace_files(self, tmp_path, monkeypatch):
        monkeypatch.setattr("autospec.SPECS_DIR", tmp_path)
        (tmp_path / "Test.tla").write_text("---- MODULE Test ----\n====")
        (tmp_path / "Test_TTrace_12345.tla").write_text("trace artifact")
        specs = load_current_specs()
        assert "Test.tla" in specs
        assert "Test_TTrace_12345.tla" not in specs
