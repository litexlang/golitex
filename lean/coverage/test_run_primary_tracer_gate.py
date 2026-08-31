#!/usr/bin/env python3
"""Pure run-envelope parser tests for run_primary_tracer_gate.py."""

from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path


PATH = Path(__file__).resolve().parent / "run_primary_tracer_gate.py"
SPEC = importlib.util.spec_from_file_location("run_primary_tracer_gate", PATH)
assert SPEC and SPEC.loader
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class PrimaryTracerParserTests(unittest.TestCase):
    def test_accepts_one_run_envelope(self) -> None:
        run = json.dumps(
            {"kind": "run", "ok": True, "statement_results": [], "error": None}
        )
        self.assertIs(GATE.run_envelope(run)["ok"], True)

    def test_rejects_another_json_kind(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a run envelope"):
            GATE.run_envelope('{"kind":"artifact","ok":true}')

    def test_rejects_multiple_json_documents(self) -> None:
        with self.assertRaisesRegex(ValueError, "not one JSON document"):
            GATE.run_envelope('{"kind":"run"}\n{"kind":"run"}')


if __name__ == "__main__":
    unittest.main()
