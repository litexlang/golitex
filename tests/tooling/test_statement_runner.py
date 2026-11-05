"""Keep the Stmt corpus gate strict about current Normal JSON failures."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "statement_runner", ROOT / "examples/test_statements/run.py")
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)
FUNCTION_SPEC = importlib.util.spec_from_file_location(
    "function_set_runner", ROOT / "examples/test_function_sets/run.py")
FUNCTION_RUNNER = importlib.util.module_from_spec(FUNCTION_SPEC)
FUNCTION_SPEC.loader.exec_module(FUNCTION_RUNNER)


class StatementFailureContractTests(unittest.TestCase):
    def setUp(self):
        self.output = {
            "kind": "run", "detail": "normal", "run_result": "failure",
            "session_terminated": False, "termination": None,
            "statement_results": [{"statement_result": "rejected", "statement": "1 = 2"}],
            "errors": [{"statement_index": 0, "phase": "search_proof",
                        "message": "Could not prove the goal."}],
        }
        self.expect = {"success": False, "statement_success": [False],
                       "failed_phase": ["search_proof"]}

    def check(self, output=None, expect=None):
        completed = subprocess.CompletedProcess(
            [], 1, json.dumps(output or self.output), "")
        with patch.object(RUNNER.subprocess, "run", return_value=completed):
            return RUNNER.run(Path("litex"), "contract", [], True, expect or self.expect)

    def test_top_level_error_is_accepted(self):
        self.assertTrue(self.check()["matches"])

    def test_wrong_phase_is_rejected(self):
        self.output["errors"][0]["phase"] = "parse"
        self.assertIn("wrong failure phase", self.check()["errors"])

    def test_missing_or_foreign_error_is_rejected(self):
        for diagnostics in [[], [{"statement_index": 1, "phase": "search_proof"}]]:
            with self.subTest(diagnostics=diagnostics):
                self.output["errors"] = diagnostics
                self.assertIn("failure diagnostic indices differ", self.check()["errors"])

    def test_parse_rejection_retains_prefix_and_message(self):
        self.output["statement_results"].insert(0, {"statement_result": "accepted"})
        self.output["errors"] = [{"statement_index": 1, "phase": "parse",
                                  "message": "undefined name `missing`"}]
        expected = {"success": False, "statement_success": [True, False],
                    "failed_phase": ["parse"], "error_contains": "undefined name `missing`"}
        self.assertTrue(self.check(expect=expected)["matches"])
        changed = copy.deepcopy(self.output)
        changed["errors"][0]["message"] = "another parse error"
        self.assertIn("wrong failure diagnostic", self.check(changed, expected)["errors"])

    def test_terminated_session_is_not_a_soft_failure(self):
        self.output.update(session_terminated=True, termination="stopped")
        self.assertIn("expected a soft statement failure", self.check()["errors"])

    def test_function_set_runner_requires_the_corresponding_diagnostic(self):
        for index, expected in [(0, "reject"), (1, "infrastructure_failure")]:
            with self.subTest(index=index):
                self.output["errors"][0]["statement_index"] = index
                completed = subprocess.CompletedProcess([], 1, json.dumps(self.output), "")
                with patch.object(FUNCTION_RUNNER.subprocess, "run", return_value=completed):
                    result = FUNCTION_RUNNER.evaluate(ROOT / "fixture.lit")
                self.assertEqual(result["observed"], expected)


if __name__ == "__main__":
    unittest.main()
