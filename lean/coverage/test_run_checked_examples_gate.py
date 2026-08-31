#!/usr/bin/env python3
"""Pure total-reconciliation tests for the checked-example gate."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


PATH = Path(__file__).resolve().parent / "run_checked_examples_gate.py"
SPEC = importlib.util.spec_from_file_location("run_checked_examples_gate", PATH)
assert SPEC and SPEC.loader
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class CheckedExampleGateTests(unittest.TestCase):
    def test_totals_reconcile_classes_and_forbidden_rows(self) -> None:
        rows = [
            {"kernel_class": "pass", "forbidden_hits": []},
            {"kernel_class": "kernel_reject", "forbidden_hits": ["2:sorry"]},
            {"kernel_class": "infrastructure_failure", "forbidden_hits": []},
        ]
        self.assertEqual(
            GATE.totals(rows),
            {"registered": 3, "pass": 1, "kernel_reject": 1, "infrastructure_failure": 1, "forbidden_rows": 1},
        )


if __name__ == "__main__":
    unittest.main()
