#!/usr/bin/env python3
"""Pure contract tests for the non-destructive example matrix runner."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).resolve().parent / "kernel_check_examples.py"
SPEC = importlib.util.spec_from_file_location("kernel_check_examples", MODULE_PATH)
assert SPEC and SPEC.loader
MATRIX = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MATRIX
SPEC.loader.exec_module(MATRIX)


class ExampleMatrixContractTests(unittest.TestCase):
    def stable(self, **overrides: object) -> bool:
        values: dict[str, object] = {
            "compiler_before": "compiler",
            "compiler_after": "compiler",
            "examples_before": "examples",
            "examples_after": "examples",
            "lean_before": "lean",
            "lean_after": "lean",
            "rust_before_build": "rust",
            "rust_after_build": "rust",
            "rust_before_matrix": "rust",
            "rust_after_matrix": "rust",
            "olean_errors_after": [],
        }
        values.update(overrides)
        return MATRIX.snapshot_is_stable(**values)

    def test_stable_snapshot_requires_all_surfaces_to_match(self) -> None:
        self.assertTrue(self.stable())
        self.assertFalse(self.stable(compiler_after="changed"))
        self.assertFalse(self.stable(examples_after="changed"))
        self.assertFalse(self.stable(lean_after="changed"))
        self.assertFalse(self.stable(olean_errors_after=["missing Core.olean"]))

    def test_stable_snapshot_rejects_intermediate_rust_drift(self) -> None:
        self.assertFalse(self.stable(rust_after_build="intermediate"))
        self.assertFalse(self.stable(rust_before_matrix="intermediate"))

    def test_kernel_class_separates_infrastructure_from_rejection(self) -> None:
        self.assertEqual(MATRIX.kernel_class(None, ""), "not_run")
        self.assertEqual(MATRIX.kernel_class(0, ""), "pass")
        self.assertEqual(
            MATRIX.kernel_class(1, "object file Core.olean does not exist"),
            "infrastructure_failure",
        )
        self.assertEqual(MATRIX.kernel_class(1, "type mismatch"), "kernel_reject")

    def test_first_error_recognizes_lean_diagnostic_codes(self) -> None:
        output = (
            "Litex.first : Prop\n"
            "gate.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `x`\n"
        )
        self.assertEqual(
            MATRIX.first_error(output),
            "gate.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `x`",
        )
        self.assertEqual(
            MATRIX.first_error("error[E0425]: cannot find function `route`"),
            "error[E0425]: cannot find function `route`",
        )

    def test_forbidden_output_scan_reports_exact_lines(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "generated.lean"
            path.write_text(
                "theorem good : True := True.intro\n"
                "theorem hole : True := by sorry\n"
                "#check Litex.Object\n",
                encoding="utf-8",
            )
            self.assertEqual(
                MATRIX.forbidden_output_hits(path),
                [
                    "2:theorem hole : True := by sorry",
                    "3:#check Litex.Object",
                ],
            )

    def test_clear_generated_output_prevents_stale_hash_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "old.generated.lean"
            path.write_text("stale", encoding="utf-8")
            MATRIX.clear_generated_output(path)
            self.assertFalse(path.exists())


if __name__ == "__main__":
    unittest.main()
