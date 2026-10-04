from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Sequence

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
PREDEPLOY_GATE_PATH = REPOSITORY_ROOT / ".github" / "scripts" / "predeploy_gate.py"
PREDEPLOY_GATE_SPEC = importlib.util.spec_from_file_location(
    "predeploy_gate", PREDEPLOY_GATE_PATH
)
if PREDEPLOY_GATE_SPEC is None or PREDEPLOY_GATE_SPEC.loader is None:
    raise RuntimeError(f"cannot load predeploy gate from {PREDEPLOY_GATE_PATH}")
PREDEPLOY_GATE = importlib.util.module_from_spec(PREDEPLOY_GATE_SPEC)
sys.modules[PREDEPLOY_GATE_SPEC.name] = PREDEPLOY_GATE
PREDEPLOY_GATE_SPEC.loader.exec_module(PREDEPLOY_GATE)

from predeploy_gate import (
    GATES,
    ProcessController,
    ProcessOutcome,
    TEXTBOOKS,
    Textbook,
    TextbookFile,
    cargo_test_command,
    cargo_test_counts,
    collect_textbook_files,
    file_result_from_completed,
    run_gates,
    run_cargo_test,
    run_textbook_file,
    textbook_file_command,
)


class PredeployGateTest(unittest.TestCase):
    def test_deployment_textbook_allowlist_is_explicit(self) -> None:
        self.assertEqual(
            [(book.name, book.module_path.as_posix()) for book in TEXTBOOKS],
            [
                ("Analysis", "scripts/Analysis/textbook"),
                ("MIL", "scripts/mathematics_in_litex/textbook"),
                ("Mechanics", "scripts/The-Mechanics-of-Litex-Proof/textbook"),
                ("LADR", "scripts/linear_algebra_done_right/textbook"),
                ("NTFB", "scripts/number_theory_for_beginners/textbook"),
            ],
        )

    def test_commands_use_dedicated_release_tests(self) -> None:
        self.assertEqual(
            GATES,
            (
                ("docs", "run_docs_markdown_files"),
                ("examples", "run_examples_only"),
                ("showcases", "run_showcases"),
            ),
        )
        self.assertEqual(
            cargo_test_command("run_examples_only"),
            [
                "cargo",
                "test",
                "--release",
                "run_examples_only",
                "--",
                "--nocapture",
            ],
        )
        self.assertEqual(
            cargo_test_command("run_showcases"),
            [
                "cargo",
                "test",
                "--release",
                "run_showcases",
                "--",
                "--nocapture",
            ],
        )

    def test_gates_start_in_parallel_and_keep_registration_order(self) -> None:
        barrier = threading.Barrier(3, timeout=1)

        def fake_runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            barrier.wait()
            test_name = command[3]
            delays = {
                "run_docs_markdown_files": 0.01,
                "run_examples_only": 0.02,
                "run_showcases": 0.03,
            }
            time.sleep(delays[test_name])
            return subprocess.CompletedProcess(command, 0, stdout=(
                "running 1 test\n" + f"test {test_name} ... ok\n" +
                "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
                "0 filtered out; finished in 0.00s\n"
            ))

        results = run_gates(Path("/repo"), runner=fake_runner)

        self.assertEqual(
            [result.label for result in results],
            ["docs", "examples", "showcases"],
        )
        self.assertTrue(all(result.returncode == 0 for result in results))
        self.assertTrue(all(result.wall_seconds > 0 for result in results))
        self.assertTrue(all(result.status == "success" for result in results))
        self.assertTrue(all(result.tests_executed == 1 for result in results))

    def test_cargo_gate_rejects_zero_execution_on_both_process_paths(self) -> None:
        output = (
            "running 0 tests\n"
            "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; "
            "800 filtered out; finished in 0.00s\n"
        )

        def runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            return subprocess.CompletedProcess(command, 0, stdout=output)

        class Controller:
            def run(self, *_: object, **__: object) -> ProcessOutcome:
                return ProcessOutcome("completed", 0, output, "", 0.01)

        for controller in [None, Controller()]:
            with self.subTest(controller=controller):
                result = run_cargo_test(Path("/repo"), "examples", "missing_filter",
                                        runner, controller)  # type: ignore[arg-type]
                self.assertEqual(result.status, "failed")
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.tests_selected, 0)
                self.assertEqual(result.tests_executed, 0)
                self.assertIn("zero tests executed", result.output)
                self.assertIn("missing_filter", result.output)

    def test_cargo_counts_accept_real_execution_among_empty_targets(self) -> None:
        empty = ("running 0 tests\n"
                 "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; "
                 "40 filtered out; finished in 0.00s\n")
        nonempty = ("running 2 tests\ntest first ... ok\ntest second ... ok\n"
                    "test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; "
                    "3 filtered out; finished in 0.01s\n")
        self.assertEqual(cargo_test_counts(empty + nonempty + empty), (2, 2, None))

    def test_cargo_counts_reject_missing_inconsistent_or_failed_evidence(self) -> None:
        valid = ("running 1 test\n"
                 "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
                 "0 filtered out; finished in 0.00s\n")
        invalid = [
            "", "test output\n", "running 1 test\n",
            valid + "running 1 test\n",
            valid.replace("running 1 test", "running 2 tests"),
            valid.split("\n", 1)[1],
            valid.replace("ok. 1 passed; 0 failed", "FAILED. 0 passed; 1 failed"),
            valid.replace("1 passed; 0 failed; 0 ignored", "0 passed; 0 failed; 1 ignored"),
            valid.replace("1 passed; 0 failed; 0 ignored; 0 measured", "0 passed; 0 failed; 0 ignored; 1 measured"),
            valid.replace("0 filtered out", "invalid summary"),
            "running 1 test\n" + valid,
        ]
        for output in invalid:
            with self.subTest(output=output):
                self.assertIsNotNone(cargo_test_counts(output)[2])

    def test_cargo_controller_failure_and_cancellation_cannot_be_success(self) -> None:
        valid = ("running 1 test\n"
                 "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
                 "0 filtered out; finished in 0.00s\n")
        for status, code in [("completed", 1), ("cancelled", -15), ("not_started", None)]:
            class Controller:
                timeout_seconds = 1.0

                def run(self, *_: object, **__: object) -> ProcessOutcome:
                    return ProcessOutcome(status, code, valid, "", 0.01)

            with self.subTest(status=status):
                result = run_cargo_test(Path("/repo"), "examples", "fixture",
                                        controller=Controller())  # type: ignore[arg-type]
                self.assertNotEqual(result.status, "success")
                self.assertIsNone(result.tests_executed)

    def test_failure_is_preserved_per_gate(self) -> None:
        def fake_runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            returncode = 1 if command[3] == "run_showcases" else 0
            return subprocess.CompletedProcess(command, returncode, stdout="test output\n")

        results = run_gates(Path("/repo"), runner=fake_runner)

        self.assertEqual([result.returncode for result in results], [0, 0, 1])
        self.assertEqual(results[2].output, "test output\n")
        self.assertTrue(all(result.wall_seconds >= 0 for result in results))

    def test_global_deadline_stops_running_processes_and_blocks_new_ones(self) -> None:
        controller = ProcessController(0.15)
        fast = [sys.executable, "-c", "print('done')"]
        slow = [
            sys.executable,
            "-c",
            "import time; print('running', flush=True); time.sleep(10)",
        ]

        started = time.perf_counter()
        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = [
                executor.submit(controller.run, fast, cwd=REPOSITORY_ROOT),
                executor.submit(controller.run, slow, cwd=REPOSITORY_ROOT),
                executor.submit(controller.run, slow, cwd=REPOSITORY_ROOT),
            ]
            outcomes = [future.result() for future in futures]

        self.assertEqual(outcomes[0].status, "completed")
        self.assertEqual(outcomes[0].returncode, 0)
        self.assertEqual(
            [outcome.status for outcome in outcomes[1:]],
            ["cancelled", "cancelled"],
        )
        self.assertLess(time.perf_counter() - started, 2.0)

        not_started = controller.run(fast, cwd=REPOSITORY_ROOT)
        self.assertEqual(not_started.status, "not_started")

    def test_global_cancellation_reports_last_textbook_statement(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repository_root = Path(temporary_directory)
            path = repository_root / "chapter.lit"
            path.write_text("have x R\n\nx = x\n", encoding="utf-8")
            textbook_file = TextbookFile(
                Textbook("Book", Path("scripts/Book/textbook")), path, 1, 1
            )

            class CancelledController:
                timeout_seconds = 240.0

                def run(self, *_: object, **__: object) -> ProcessOutcome:
                    return ProcessOutcome(
                        "cancelled",
                        -15,
                        "",
                        f"repository statement {path}:1: 2.00 ms\n",
                        240.0,
                    )

            result = run_textbook_file(
                repository_root,
                Path("/repo/target/release/litex"),
                textbook_file,
                600.0,
                controller=CancelledController(),  # type: ignore[arg-type]
            )

            self.assertEqual(result.status, "cancelled")
            self.assertEqual(result.line, 3)
            self.assertEqual(result.statement, "x = x")
            self.assertIn("240s global deadline", result.message or "")

    def test_registered_textbook_files_preserve_export_order(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repository_root = Path(temporary_directory)
            module = repository_root / "scripts" / "Book" / "textbook"
            module.mkdir(parents=True)
            (module / "first.lit").write_text("1 = 1\n", encoding="utf-8")
            (module / "second.lit").write_text("2 = 2\n", encoding="utf-8")
            (module / "support").mkdir()
            (module / "litex.config").write_text(
                '[hierarchy]\nmodule\n\n[export]\nfirst = "./first.lit"\n'
                'support = "./support"\nsecond = "./second.lit"\n',
                encoding="utf-8",
            )

            files = collect_textbook_files(
                repository_root,
                [Textbook("Book", Path("scripts/Book/textbook"))],
            )

            self.assertEqual([item.path.name for item in files], ["first.lit", "second.lit"])
            self.assertEqual([item.book_index for item in files], [1, 2])
            self.assertTrue(all(item.book_total == 2 for item in files))

    def test_file_runner_requires_consistent_envelope_and_extracts_failure(self) -> None:
        textbook_file = TextbookFile(
            Textbook("Book", Path("scripts/Book/textbook")),
            Path("/repo/scripts/Book/textbook/chapter.lit"),
            1,
            1,
        )
        envelope = json.dumps({
            "kind": "run", "success": False, "target": "file",
            "path": "/repo/scripts/Book/textbook/chapter.lit",
            "statement_results": [{
                "success": True, "statement": "1 = 1",
            }, {
                "success": False, "statement": "1 = 0",
                "why_failed": {
                    "line": 42,
                    "path": "/repo/scripts/Book/textbook/chapter.lit",
                    "message": "verification failed",
                    "failed_goal": "1 = 0",
                },
            }],
            "session_error": None,
        })

        result = file_result_from_completed(
            Path("/repo"),
            textbook_file,
            subprocess.CompletedProcess([], 1, stdout=envelope, stderr=""),
            0.5,
        )

        self.assertEqual(result.status, "failed")
        self.assertEqual(
            result.source_path, "scripts/Book/textbook/chapter.lit"
        )
        self.assertEqual(result.line, 42)
        self.assertEqual(result.statement, "1 = 0")
        self.assertEqual(result.message, "verification failed")

    def test_timeout_reports_next_statement_after_last_profile_event(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repository_root = Path(temporary_directory)
            path = repository_root / "scripts" / "Book" / "textbook" / "chapter.lit"
            path.parent.mkdir(parents=True)
            path.write_text("have x R\n\nx = x\n", encoding="utf-8")
            textbook_file = TextbookFile(
                Textbook("Book", Path("scripts/Book/textbook")), path, 1, 1
            )

            def timeout_runner(
                command: Sequence[str], **_: object
            ) -> subprocess.CompletedProcess[str]:
                raise subprocess.TimeoutExpired(
                    command,
                    0.01,
                    output="",
                    stderr=f"repository statement {path}:1: 2.00 ms\n",
                )

            result = run_textbook_file(
                repository_root,
                Path("/repo/target/release/litex"),
                textbook_file,
                0.01,
                runner=timeout_runner,
            )

            self.assertEqual(result.status, "timeout")
            self.assertEqual(result.line, 3)
            self.assertEqual(result.statement, "x = x")
            self.assertIn("inferred", result.message or "")

    def test_timeout_location_skips_top_level_documentation_blocks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repository_root = Path(temporary_directory)
            path = repository_root / "chapter.lit"
            path.write_text(
                'have x R\n\n"""\nchapter note\n"""\n\nthm next:\n    ? x = x\n',
                encoding="utf-8",
            )
            textbook_file = TextbookFile(
                Textbook("Book", Path("scripts/Book/textbook")), path, 1, 1
            )

            def timeout_runner(
                command: Sequence[str], **_: object
            ) -> subprocess.CompletedProcess[str]:
                raise subprocess.TimeoutExpired(
                    command,
                    0.01,
                    output="",
                    stderr=f"repository statement {path}:1: 2.00 ms\n",
                )

            result = run_textbook_file(
                repository_root,
                Path("/repo/target/release/litex"),
                textbook_file,
                0.01,
                runner=timeout_runner,
            )

            self.assertEqual(result.line, 7)
            self.assertEqual(result.statement, "thm next:")

    def test_invalid_runner_output_reports_termination_signal(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            repository_root = Path(temporary_directory)
            path = repository_root / "chapter.lit"
            path.write_text("have x R\n\nx = x\n", encoding="utf-8")
            textbook_file = TextbookFile(
                Textbook("Book", Path("scripts/Book/textbook")), path, 1, 1
            )

            result = file_result_from_completed(
                repository_root,
                textbook_file,
                subprocess.CompletedProcess(
                    [],
                    -9,
                    stdout="",
                    stderr=f"repository statement {path}:1: 2.00 ms\n",
                ),
                2.0,
            )

            self.assertEqual(result.status, "contract_error")
            self.assertIn("terminated by signal 9", result.message or "")
            self.assertEqual(result.line, 3)
            self.assertEqual(result.statement, "x = x")

    def test_textbook_command_uses_current_file_entry(self) -> None:
        self.assertEqual(
            textbook_file_command(Path("/repo/litex"), Path("/repo/book/ch1.lit")),
            [
                "/repo/litex",
                "-f",
                "/repo/book/ch1.lit",
            ],
        )

    def test_run_contract_rejects_inconsistent_or_old_payloads(self) -> None:
        valid = {"kind": "run", "target": "file", "path": "/repo/ch.lit",
                 "success": True, "statement_results": [{"success": True}],
                 "session_error": None}
        self.assertIsNone(PREDEPLOY_GATE.run_file_contract_error(valid, 0))
        for change, code in [
            ({"kind": "artifact"}, 0), ({"target": "eval"}, 0),
            ({"path": None}, 0), ({"success": "true"}, 0), ({}, -9),
            ({"statement_results": [{"success": False}]}, 0),
            ({"statement_results": [{}]}, 0), ({"statement_results": None}, 0),
            ({"session_error": "internal_bug: Litex internal bug"}, 0),
            ({"session_error": {}}, 0), ({"success": False}, 1),
        ]:
            with self.subTest(change=change, code=code):
                self.assertIsNotNone(PREDEPLOY_GATE.run_file_contract_error({**valid, **change}, code))

    def test_internal_bug_is_a_failed_file_with_the_original_message(self) -> None:
        file = TextbookFile(Textbook("Book", Path("scripts/Book/textbook")),
                            Path("/repo/ch.lit"), 1, 1)
        message = "internal_bug: Litex internal bug: inferred fact failed WD"
        envelope = {"kind": "run", "target": "file", "path": "/repo/ch.lit",
                    "success": False, "statement_results": [], "session_error": message}
        result = file_result_from_completed(Path("/repo"), file,
                  subprocess.CompletedProcess([], 1, stdout=json.dumps(envelope), stderr=""), 0.1)
        self.assertEqual(result.status, "failed")
        self.assertEqual(result.message, message)
        self.assertEqual(result.source_path, "ch.lit")


if __name__ == "__main__":
    unittest.main()
