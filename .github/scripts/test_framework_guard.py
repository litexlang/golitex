#!/usr/bin/env python3
"""Unit tests for `.github/scripts/framework_guard.py`."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import framework_guard  # noqa: E402


class FrameworkGuardTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp_dir = tempfile.TemporaryDirectory(prefix="litex-fw-guard-")
        self.addCleanup(self.temp_dir.cleanup)
        self.repo = Path(self.temp_dir.name)
        self.env = {
            **os.environ,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
        }
        self.env.pop("ALLOW_FRAMEWORK_UNLOCK", None)
        self.env.pop("ALLOW_TIER2_EDIT", None)

        self.git("init", "-q")
        self.git("config", "user.name", "Guard Test")
        self.git("config", "user.email", "guard@example.invalid")
        self.git("config", "commit.gpgsign", "false")

        for rel_path in framework_guard.TIER1_FROZEN_BACKBONE:
            p = self.repo / rel_path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(f"// Tier 1 frozen backbone: {rel_path}\npub fn backbone() {{}}\n", encoding="utf-8")

        for rel_path in (
            *framework_guard.TIER2_ENUM_REGISTRIES,
            *framework_guard.TIER2_DISPATCH_REGISTRIES,
        ):
            p = self.repo / rel_path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(
                f"// Tier 2 registry: {rel_path}\npub enum Branch {{\n    ArmA,\n}}\n",
                encoding="utf-8",
            )

        rc = framework_guard.main(["--update-lock", "--repo-root", str(self.repo)])
        self.assertEqual(rc, 0)
        self.git("add", "-A")
        self.git("commit", "-qm", "initial framework lock")

    def git(self, *args: str) -> str:
        return subprocess.check_output(
            ["git", "-C", str(self.repo), *args],
            env=self.env,
            text=True,
        )

    def run_guard(self, *args: str, extra_env: dict | None = None) -> subprocess.CompletedProcess[str]:
        env = {**self.env, **(extra_env or {})}
        return subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "framework_guard.py"), "--repo-root", str(self.repo), *args],
            cwd=self.repo,
            env=env,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_clean_state_passes_all_modes(self) -> None:
        for flag in ("--staged", "--worktree", "--ci"):
            res = self.run_guard(flag)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_tier1_edit_blocked_until_lock_updated_and_unlocked(self) -> None:
        target = self.repo / "src/execute/exec_stmt.rs"
        target.write_text("// modified backbone\npub fn backbone() { let _ = 1; }\n", encoding="utf-8")
        self.git("add", "src/execute/exec_stmt.rs")

        # Blocked with hash mismatch (rc=2)
        res = self.run_guard("--staged")
        self.assertEqual(res.returncode, 2)
        self.assertIn("src/execute/exec_stmt.rs", res.stderr)

        # Even with ALLOW_FRAMEWORK_UNLOCK=1, hash mismatch without --update-lock still fails!
        res_mismatch = self.run_guard("--staged", extra_env={"ALLOW_FRAMEWORK_UNLOCK": "1"})
        self.assertEqual(res_mismatch.returncode, 2)

        # Update lock file and stage it
        upd = self.run_guard("--update-lock")
        self.assertEqual(upd.returncode, 0)
        self.git("add", ".github/framework_lock.json")

        # Without ALLOW_FRAMEWORK_UNLOCK=1, commit is still gated with warning (rc=3)
        res_warn = self.run_guard("--staged")
        self.assertEqual(res_warn.returncode, 3)
        self.assertIn("ALLOW_FRAMEWORK_UNLOCK=1", res_warn.stderr)

        # With ALLOW_FRAMEWORK_UNLOCK=1, commit passes
        res_ok = self.run_guard("--staged", extra_env={"ALLOW_FRAMEWORK_UNLOCK": "1"})
        self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

        # Commit and verify CI mode passes while emitting GitHub warning annotation
        self.git("commit", "-qm", "intentional backbone update")
        res_ci = self.run_guard("--ci")
        self.assertEqual(res_ci.returncode, 0, res_ci.stdout + res_ci.stderr)
        self.assertIn("::warning title=Tier 1 Framework Lock Updated::", res_ci.stdout)

    def test_tier2_append_only_passes_without_override(self) -> None:
        target = self.repo / "src/execute/dispatch_stmt.rs"
        original = target.read_text(encoding="utf-8")
        target.write_text(original + "// appended new dispatch helper\npub fn new_arm() {}\n", encoding="utf-8")
        self.git("add", "src/execute/dispatch_stmt.rs")

        res = self.run_guard("--staged")
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("Tier 2 append-only branch addition: src/execute/dispatch_stmt.rs", res.stdout)

    def test_tier2_modification_warns_unless_authorized(self) -> None:
        target = self.repo / "src/execute/dispatch_stmt.rs"
        target.write_text("// Tier 2 registry\npub enum Branch {\n    RenamedArm,\n}\n", encoding="utf-8")
        self.git("add", "src/execute/dispatch_stmt.rs")

        res_warn = self.run_guard("--staged")
        self.assertEqual(res_warn.returncode, 4)
        self.assertIn("ALLOW_TIER2_EDIT=1", res_warn.stderr)

        res_ok = self.run_guard("--staged", extra_env={"ALLOW_TIER2_EDIT": "1"})
        self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

    def test_tier2_forbidden_state_token_always_rejected(self) -> None:
        target = self.repo / "src/execute/dispatch_stmt.rs"
        original = target.read_text(encoding="utf-8")
        target.write_text(original + "// bad: env.merge_from(other);\n", encoding="utf-8")
        self.git("add", "src/execute/dispatch_stmt.rs")

        res = self.run_guard("--staged", extra_env={"ALLOW_TIER2_EDIT": "1"})
        self.assertEqual(res.returncode, 2)
        self.assertIn("merge_from(", res.stderr)


if __name__ == "__main__":
    unittest.main()
