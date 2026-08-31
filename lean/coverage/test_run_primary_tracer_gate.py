#!/usr/bin/env python3
"""Pure summary parser tests for run_primary_tracer_gate.py."""

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
    def test_selects_last_run_summary(self) -> None:
        statement = json.dumps({"schema": "litex.statement-result.v2", "outcome": "success"}, indent=2)
        summary = json.dumps({"result": "success", "output_type": "run summary", "axioms": 0}, indent=2)
        self.assertEqual(GATE.run_summary(statement + "\n" + summary)["result"], "success")

    def test_rejects_output_without_summary(self) -> None:
        with self.assertRaisesRegex(ValueError, "no run summary"):
            GATE.run_summary('{"result":"success"}')


if __name__ == "__main__":
    unittest.main()
