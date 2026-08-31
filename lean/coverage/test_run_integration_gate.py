#!/usr/bin/env python3
"""Pure parser tests for run_integration_gate.py."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).resolve().parent / "run_integration_gate.py"
SPEC = importlib.util.spec_from_file_location("run_integration_gate", MODULE_PATH)
assert SPEC and SPEC.loader
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class IntegrationGateParserTests(unittest.TestCase):
    def test_parse_test_totals_and_failure_names(self) -> None:
        output = (
            "failures:\n\nfailures:\n"
            "    first_failure\n"
            "    second_failure\n\n"
            "test result: FAILED. 55 passed; 2 failed; 0 ignored; "
            "0 measured; 0 filtered out; finished in 5.38s\n"
        )
        totals = GATE.parse_test_totals(output)
        self.assertEqual(totals["passed"], 55)
        self.assertEqual(totals["failed"], 2)
        self.assertEqual(totals["duration_seconds"], 5.38)
        self.assertEqual(
            GATE.parse_failure_names(output),
            ["first_failure", "second_failure"],
        )

    def test_parse_success_has_no_failures(self) -> None:
        output = (
            "test result: ok. 3 passed; 0 failed; 0 ignored; "
            "0 measured; 0 filtered out; finished in 0.01s\n"
        )
        self.assertEqual(GATE.parse_failure_names(output), [])
        self.assertEqual(GATE.parse_test_totals(output)["passed"], 3)

    def test_cargo_json_selects_exact_test_binary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / "test-bin"
            binary.touch()
            message = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "target": {"name": GATE.TEST_NAME},
                    "executable": str(binary),
                }
            )
            self.assertEqual(GATE.cargo_test_binary(message), binary.resolve())

    def test_cargo_first_error_prefers_structured_diagnostic(self) -> None:
        output = json.dumps(
            {
                "reason": "compiler-message",
                "message": {
                    "level": "error",
                    "message": "cannot find type `RunOptions`",
                    "rendered": "error[E0412]: cannot find type `RunOptions`\n --> src/api.rs:1:1",
                },
            }
        )
        self.assertEqual(
            GATE.cargo_first_error(output, "error: build failed"),
            "error[E0412]: cannot find type `RunOptions` | --> src/api.rs:1:1",
        )

    def test_cargo_first_error_has_plain_fallback(self) -> None:
        self.assertEqual(
            GATE.cargo_first_error("", "error: build failed"),
            "error: build failed",
        )


if __name__ == "__main__":
    unittest.main()
