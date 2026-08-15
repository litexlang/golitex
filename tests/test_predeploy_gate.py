from __future__ import annotations

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

REPOSITORY_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPOSITORY_ROOT))

from tools.predeploy_gate import (
    GATES,
    ProcessController,
    ProcessOutcome,
    TEXTBOOKS,
    Textbook,
    TextbookFile,
    cargo_test_command,
    collect_textbook_files,
    file_result_from_completed,
    run_gates,
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

    def test_gates_start_in_parallel_and_keep_registration_order(self) -> None:
        barrier = threading.Barrier(2, timeout=1)

        def fake_runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            barrier.wait()
            test_name = command[3]
            time.sleep(0.01 if test_name == "run_docs_markdown_files" else 0.02)
            return subprocess.CompletedProcess(command, 0, stdout=f"{test_name} passed\n")

        results = run_gates(Path("/repo"), runner=fake_runner)

        self.assertEqual([result.label for result in results], ["docs", "examples"])
        self.assertTrue(all(result.returncode == 0 for result in results))
        self.assertTrue(all(result.wall_seconds > 0 for result in results))

    def test_failure_is_preserved_per_gate(self) -> None:
        def fake_runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            returncode = 1 if command[3] == "run_examples_only" else 0
            return subprocess.CompletedProcess(command, returncode, stdout="test output\n")

        results = run_gates(Path("/repo"), runner=fake_runner)

        self.assertEqual([result.returncode for result in results], [0, 1])
        self.assertEqual(results[1].output, "test output\n")
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
        successful_prefix = json.dumps(
            {
                "result": "success",
                "line": 1,
                "statement": "1 = 1",
            }
        )
        error_trace = json.dumps(
            {
                "error_type": "VerifyError",
                "line": 42,
                "path": "/repo/scripts/Book/textbook/chapter.lit",
                "message": "verification failed",
                "statement": "1 = 0",
                "previous_error": {"failed_goal": "1 = 0"},
            }
        )
        envelope = json.dumps(
            {
                "runner": "litex-runner",
                "runner_version": "0.1",
                "result": "error",
                "ok": False,
                "target": {"kind": "file", "label": "entry"},
                "error": None,
                "trace": successful_prefix + "\n\n" + error_trace,
            }
        )

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

    def test_textbook_command_uses_structured_file_runner(self) -> None:
        self.assertEqual(
            textbook_file_command(Path("/repo/litex"), Path("/repo/book/ch1.lit")),
            [
                "/repo/litex",
                "-compact",
                "-runner",
                "-f",
                "/repo/book/ch1.lit",
            ],
        )


if __name__ == "__main__":
    unittest.main()
