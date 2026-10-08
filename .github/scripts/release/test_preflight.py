#!/usr/bin/env python3
"""Focused tests for the local release preflight."""

from __future__ import annotations

import json
import subprocess
import sys
import tarfile
import tempfile
import unittest
import xml.etree.ElementTree as ET
from unittest.mock import patch
from pathlib import Path


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIRECTORY.parents[2]
PRIVATE_ROOT = REPOSITORY_ROOT / "private"
PRIVATE_ROOT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(SCRIPT_DIRECTORY))

import generate_wix_std  # noqa: E402
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

    def test_run_contract_requires_exit_zero_and_successful_statements(self) -> None:
        successful = json.dumps(
            {
                "kind": "run",
                "success": True,
                "detail": "normal",
                "target": "file",
                "path": "smoke.lit",
                "statement_results": [{"success": True, "statement": "1 = 1"}],
                "session_error": None,
            }
        )
        preflight.validate_run_output(successful, 0)
        with self.assertRaises(preflight.PreflightError):
            preflight.validate_run_output(successful, 1)
        for change in [
            {"success": False},
            {"session_error": {"type": "parse_error"}},
            {"statement_results": []},
            {"statement_results": [{"success": False}]},
            {"kind": "artifact"},
        ]:
            failed = json.loads(successful)
            failed.update(change)
            with self.subTest(change=change), self.assertRaises(preflight.PreflightError):
                preflight.validate_run_output(json.dumps(failed), 0)

    def test_version_contract_requires_matching_plain_text_and_exit_zero(self) -> None:
        version = "1.0.1-beta"
        for ending in ("", "\n", "\r\n"):
            preflight.validate_version_output(f"Litex {version}{ending}", 0, version)
        for output in (
            "Litex 1.0.0-beta\n",
            "Litex Kernel: litex 1.0.1-beta\n",
            json.dumps({"kind": "version", "ok": True, "version": version}),
            "",
            f"Litex {version}\nextra output\n",
        ):
            with self.subTest(output=output), self.assertRaises(preflight.PreflightError):
                preflight.validate_version_output(output, 0, version)
        with self.assertRaises(preflight.PreflightError):
            preflight.validate_version_output(f"Litex {version}\n", 1, version)

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

    def test_archive_smoke_uses_shipped_std_despite_inherited_env(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix="release-preflight-test.", dir=PRIVATE_ROOT
        ) as temporary_directory:
            root = Path(temporary_directory)
            package = root / "package"
            (package / "std" / "basics").mkdir(parents=True)
            (package / "litex").write_text("binary", encoding="utf-8")
            for filename in ("litex.config", "main.lit"):
                (package / "std" / "basics" / filename).write_text("", encoding="utf-8")
            archive = root / "litex_1.0.1-beta_darwin_arm64.tar.gz"
            preflight.create_archive(package, archive)
            run_json = json.dumps({
                "kind": "run", "detail": "normal", "target": "file",
                "path": "smoke.lit", "success": True, "session_error": None,
                "statement_results": [{"success": True}],
            })
            responses = [
                subprocess.CompletedProcess([], 0, "Litex 1.0.1-beta\n"),
                subprocess.CompletedProcess([], 0, run_json),
            ]
            with patch.dict(preflight.os.environ, {"LITEX_STD_PATH": str(root / "wrong-std")}), \
                    patch.object(preflight.subprocess, "run", side_effect=responses) as run, \
                    patch("builtins.print"):
                preflight.check_archive(root, archive, "1.0.1-beta")
            smoke_env = run.call_args_list[1].kwargs["env"]
            self.assertEqual(smoke_env["LITEX_STD_PATH"], str(root / "extracted" / "std"))

    def test_workflow_archive_smokes_use_shared_preflight(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text(
            encoding="utf-8"
        )
        self.assertEqual(
            workflow.count(".github/scripts/release/preflight.py --archive"), 2
        )
        self.assertIn("COPYFILE_DISABLE=1 tar -czf", workflow)
        self.assertNotIn(
            "basics::finite_set_has_bijective_index", workflow
        )

    def test_workflow_smokes_follow_current_cli_contract(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text(
            encoding="utf-8"
        )
        for obsolete in (
            "import std basics",
            "-isolated",
            "grep -F '\"success\": true'",
            "assert_match '\"success\": true', version_output",
        ):
            with self.subTest(obsolete=obsolete):
                self.assertNotIn(obsolete, workflow)
        self.assertIn('assert_equal "Litex #{version}\\n", version_output', workflow)
        self.assertIn("LITEX_STD_PATH=/usr/share/litex/std", workflow)
        self.assertIn("generate_wix_std.py", workflow)
        self.assertIn('Source="std\\basics\\litex.config"', workflow)
        self.assertIn('ComponentGroup Id="LitexStd"', workflow)
        self.assertIn('ComponentGroupRef Id="LitexStd"', workflow)

    def test_generate_wix_std_uses_package_root_sources(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix="release-preflight-test.", dir=PRIVATE_ROOT
        ) as temporary_directory:
            root = Path(temporary_directory)
            std = root / "std"
            (std / "basics").mkdir(parents=True)
            (std / "basics" / "litex.config").write_text("[export]\n", encoding="utf-8")
            (std / "basics" / "main.lit").write_text("# empty\n", encoding="utf-8")
            (std / "basics" / "todo.md").write_text("skip\n", encoding="utf-8")
            output = root / "wix" / "std.wxs"
            count = generate_wix_std.generate(std, output)
            text = output.read_text(encoding="utf-8")
            self.assertEqual(count, 2)
            self.assertIn('Source="std\\basics\\litex.config"', text)
            self.assertIn('Source="std\\basics\\main.lit"', text)
            self.assertNotIn(r'Source="..\std', text)
            self.assertIn('ComponentGroup Id="LitexStd"', text)
            self.assertNotIn("FeatureRef", text)
            self.assertIn('Directory Id="StandardLibrary" Name="std"', text)
            self.assertNotIn("todo.md", text)

    def test_wix_cli_links_every_std_component_from_product(self) -> None:
        with tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
            root = Path(temporary_directory)
            std = root / "std"
            (std / "basics").mkdir(parents=True)
            (std / "basics" / "litex.config").write_text("[export]\n")
            (std / "basics" / "main.lit").write_text("# empty\n")
            main = root / "main.wxs"
            original = '''<?xml version="1.0"?>
<Wix xmlns="http://schemas.microsoft.com/wix/2006/wi">
  <?if $(sys.BUILDARCH) = x64?>
  <?define PlatformProgramFilesFolder = "ProgramFiles64Folder"?>
  <?endif?>
  <Product Id="*">
    <Feature Id="Binaries" Level="1">
      <ComponentRef Id="binary0" />
    </Feature>
  </Product>
</Wix>
'''
            main.write_text(original)
            output = root / "std.wxs"
            command = [sys.executable, str(SCRIPT_DIRECTORY / "generate_wix_std.py"),
                       "--std", str(std), "--main", str(main), "--output", str(output)]
            subprocess.run(command, check=True, capture_output=True, text=True)
            ns = {"w": generate_wix_std.WIX_NAMESPACE}
            product = ET.fromstring(main.read_text())
            feature = product.find('./w:Product/w:Feature[@Id="Binaries"]', ns)
            self.assertIsNotNone(feature.find('w:ComponentRef[@Id="binary0"]', ns))
            refs = feature.findall("w:ComponentGroupRef", ns)
            self.assertEqual([ref.get("Id") for ref in refs], ["LitexStd"])
            fragment = ET.parse(output)
            group = fragment.find('./w:Fragment/w:ComponentGroup[@Id="LitexStd"]', ns)
            component_ids = {node.get("Id") for node in fragment.findall(".//w:Component", ns)}
            self.assertEqual(len(component_ids), 2)
            self.assertEqual({node.get("Id") for node in group}, component_ids)
            directory = fragment.find('./w:Fragment/w:DirectoryRef', ns)
            self.assertEqual(directory.get("Id"), "APPLICATIONFOLDER")
            self.assertEqual(directory.find("w:Directory", ns).get("Name"), "std")
            modified = main.read_text()
            self.assertEqual(modified.replace('\n            <ComponentGroupRef Id="LitexStd" />', ""), original)
            subprocess.run(command, check=True, capture_output=True, text=True)
            self.assertEqual(main.read_text(), modified)

    def test_wix_attachment_rejects_missing_or_ambiguous_product_feature(self) -> None:
        for body in ('<Feature Id="Other" />',
                     '<FeatureRef Id="Binaries" />',
                     '<Feature Id="Binaries"></Feature>' * 2):
            with self.subTest(body=body), tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
                main = Path(temporary_directory) / "main.wxs"
                original = f'<Wix xmlns="{generate_wix_std.WIX_NAMESPACE}"><Product>{body}</Product></Wix>'
                main.write_text(original)
                with self.assertRaisesRegex(SystemExit, "expected one Product/Binaries"):
                    generate_wix_std.attach_std_feature(main)
                self.assertEqual(main.read_text(), original)


if __name__ == "__main__":
    unittest.main()
