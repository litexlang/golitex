#!/usr/bin/env python3
"""Focused tests for the local release preflight."""

from __future__ import annotations

import json
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
REPOSITORY_ROOT = TOOLS.parents[1]
PRIVATE_ROOT = REPOSITORY_ROOT / "private"
PRIVATE_ROOT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(TOOLS))

import preflight  # noqa: E402


class ReleasePreflightTest(unittest.TestCase):
    def test_reads_only_the_package_version(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix="release-preflight-test.", dir=PRIVATE_ROOT
        ) as temporary_directory:
            cargo_toml = Path(temporary_directory) / "Cargo.toml"
            cargo_toml.write_text(
                '[package]\nname = "demo"\nversion = "1.2.3-beta"\n\n'
                '[dependencies]\nversion = "9"\n',
                encoding="utf-8",
            )
            self.assertEqual(preflight.package_version(cargo_toml), "1.2.3-beta")

    def test_release_matrix_maps_to_expected_artifacts(self) -> None:
        self.assertEqual(
            preflight.release_platform("aarch64-apple-darwin"),
            preflight.ReleasePlatform(
                "aarch64-apple-darwin", "darwin", "arm64", "litex", ".tar.gz"
            ),
        )
        self.assertEqual(
            preflight.release_platform("x86_64-pc-windows-msvc").binary_name,
            "litex.exe",
        )

    def test_runner_contract_requires_exit_zero_and_top_level_ok(self) -> None:
        successful = json.dumps(
            {
                "runner": "litex-runner",
                "runner_version": "0.1",
                "result": "success",
                "ok": True,
                "target": {"kind": "file"},
            }
        )
        preflight.validate_runner_output(successful, 0)
        with self.assertRaises(preflight.PreflightError):
            preflight.validate_runner_output(successful, 1)
        with self.assertRaises(preflight.PreflightError):
            preflight.validate_runner_output(
                json.dumps(
                    {"runner": "litex-runner", "result": "error", "ok": False}
                ),
                1,
            )

    def test_tar_archive_contains_only_root_binary_and_std(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix="release-preflight-test.", dir=PRIVATE_ROOT
        ) as temporary_directory:
            root = Path(temporary_directory)
            package = root / "package"
            (package / "std" / "basics").mkdir(parents=True)
            (package / "litex").write_text("binary", encoding="utf-8")
            (package / "std" / "basics" / "litex.config").write_text(
                "[hierarchy]\nmodule\n", encoding="utf-8"
            )
            archive = root / "litex_1.0.0_darwin_arm64.tar.gz"
            preflight.create_archive(package, archive)
            with tarfile.open(archive, "r:gz") as source:
                names = set(source.getnames())
            self.assertIn("litex", names)
            self.assertIn("std/basics/litex.config", names)
            self.assertNotIn("package/litex", names)

    def test_rejects_archive_path_traversal_and_links(self) -> None:
        for name, is_link in (
            ("../outside", False),
            ("/outside", False),
            ("link", True),
            ("std/basics/._main.lit", False),
            ("std/.DS_Store", False),
        ):
            with self.subTest(name=name, is_link=is_link):
                with self.assertRaises(preflight.PreflightError):
                    preflight.validate_archive_member(name, is_link)

    def test_workflow_archive_smokes_use_shared_preflight(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text(
            encoding="utf-8"
        )
        self.assertEqual(workflow.count("tools/release/preflight.py --archive"), 2)
        self.assertIn("COPYFILE_DISABLE=1 tar -czf", workflow)
        self.assertNotIn(
            "basics::finite_set_has_bijective_index", workflow
        )


if __name__ == "__main__":
    unittest.main()
