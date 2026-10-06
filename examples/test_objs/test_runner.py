"""Boundary checks for the corpus runner's coverage and process-result contract."""
import importlib.util
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch


sys.dont_write_bytecode = True
SUITE = Path(__file__).resolve().parent
ROOT = SUITE.parents[1]
SPEC = importlib.util.spec_from_file_location("obj_corpus_runner", SUITE / "run.py")
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


class RunnerBoundaryTests(unittest.TestCase):
    def evaluate(self, envelope, code):
        process = subprocess.CompletedProcess([], code, json.dumps(envelope), "")
        with patch.object(RUNNER.subprocess, "run", return_value=process):
            return RUNNER.evaluate(ROOT / "target/release/litex", ROOT, SUITE / "div.lit", 1)

    def test_current_ast_and_fixture_inventory(self):
        manifest = json.loads((SUITE / "coverage.json").read_text())
        self.assertEqual(RUNNER.audit(SUITE, ROOT, manifest), [])

    def test_failed_build_executes_no_fixture(self):
        process = subprocess.CompletedProcess([], 101, '', 'error: deliberate build failure')
        with patch.object(RUNNER.sys, 'argv', ['run.py', '--object', 'div']), \
                patch.object(RUNNER.subprocess, 'run', return_value=process) as launch, \
                contextlib.redirect_stderr(io.StringIO()):
            result = RUNNER.main()
        self.assertEqual(result, 1)
        self.assertEqual(launch.call_count, 1)
        self.assertEqual(launch.call_args.args[0], ['cargo', 'build', '--release'])

    def test_new_obj_variant_requires_coverage(self):
        manifest = json.loads((SUITE / "coverage.json").read_text())
        original = Path.read_text
        source_path = ROOT / manifest["ast_source"]

        def read(path, *args, **kwargs):
            source = original(path, *args, **kwargs)
            if path == source_path:
                source = source.replace("pub enum Obj {", "pub enum Obj {\n    FutureLeaf(Box<Number>),")
            return source

        with patch.object(Path, "read_text", read):
            errors = RUNNER.audit(SUITE, ROOT, manifest)
        self.assertIn("uncovered AST leaf Obj::FutureLeaf", errors)

    def test_nested_helper_variants_are_inventoried(self):
        enums = RUNNER.ast_enums((ROOT / "src/ast/obj.rs").read_text())
        self.assertIn(("AnonymousFnLiteral", "Box<AnonymousFn>"), enums["FnObjHead"])

    def test_exit_status_and_json_must_agree(self):
        for success, code in [(True, 1), (False, 0)]:
            with self.subTest(success=success, code=code):
                result = self.evaluate({"kind": "run", "success": success,
                    "statement_results": [], "session_error": None}, code)
                self.assertEqual(result["observed"], "infrastructure_failure")

    def test_real_verifier_rejection_is_distinct_from_launch_failure(self):
        envelope = {"kind": "run", "success": False, "statement_results": [
            {"success": False, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined"}}], "session_error": None}
        self.assertEqual(self.evaluate(envelope, 1)["observed"], "reject")
        self.assertEqual(self.evaluate(envelope, 2)["observed"], "infrastructure_failure")

    def test_current_parse_rejection_protocol(self):
        envelope = {"kind": "run", "success": False, "statement_results": [],
            "session_error": "parse_error: cart_dim is removed at line 2"}
        result = self.evaluate(envelope, 1)
        self.assertEqual((result["observed"], result["phase"]), ("reject", "parse"))
        self.assertEqual(self.evaluate(envelope, 2)["observed"], "infrastructure_failure")

    def test_panic_and_invalid_json_are_not_negative_test_successes(self):
        process = subprocess.CompletedProcess([], -6, "", "thread panicked")
        with patch.object(RUNNER.subprocess, "run", return_value=process):
            result = RUNNER.evaluate(ROOT / "target/release/litex", ROOT, SUITE / "div.lit", 1)
        self.assertEqual(result["observed"], "infrastructure_failure")

    def test_timeout_is_not_negative_test_success(self):
        with patch.object(RUNNER.subprocess, "run", side_effect=subprocess.TimeoutExpired([], 1)):
            result = RUNNER.evaluate(ROOT / "target/release/litex", ROOT, SUITE / "div.lit", 1)
        self.assertEqual(result["observed"], "infrastructure_failure")

    def test_hidden_failed_statement_cannot_be_positive(self):
        result = self.evaluate({"kind": "run", "success": True, "statement_results": [
            {"success": False, "why_failed": {"phase": "search_proof"}}], "session_error": None}, 0)
        self.assertEqual(result["observed"], "infrastructure_failure")


if __name__ == "__main__":
    unittest.main()
