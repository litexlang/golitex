from __future__ import annotations

import subprocess
import sys
import threading
import time
import unittest
from pathlib import Path
from typing import Sequence

REPOSITORY_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPOSITORY_ROOT))

from tools.predeploy_gate import GATES, cargo_test_command, run_gates


class PredeployGateTest(unittest.TestCase):
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

    def test_failure_is_preserved_per_gate(self) -> None:
        def fake_runner(command: Sequence[str], **_: object) -> subprocess.CompletedProcess[str]:
            returncode = 1 if command[3] == "run_examples_only" else 0
            return subprocess.CompletedProcess(command, returncode, stdout="test output\n")

        results = run_gates(Path("/repo"), runner=fake_runner)

        self.assertEqual([result.returncode for result in results], [0, 1])
        self.assertEqual(results[1].output, "test output\n")


if __name__ == "__main__":
    unittest.main()
