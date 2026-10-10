#!/usr/bin/env python3
"""Focused tests for the local release preflight."""

from __future__ import annotations

import json
import subprocess
import sys
import tarfile
import tempfile
import shutil
import unittest
import xml.etree.ElementTree as ET
from unittest.mock import Mock, patch
from pathlib import Path


SCRIPT_DIRECTORY = Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIRECTORY.parents[2]
PRIVATE_ROOT = REPOSITORY_ROOT / "private"
PRIVATE_ROOT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(SCRIPT_DIRECTORY))

import generate_wix_std  # noqa: E402
import preflight  # noqa: E402
import package_std  # noqa: E402
import package_manager_smoke  # noqa: E402


class ReleasePreflightTest(unittest.TestCase):
    def test_scoop_partial_install_is_cleaned(self) -> None:
        with tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
            root = Path(temporary_directory)
            archive = root / "archive.zip"
            archive.write_bytes(b"package")
            prefix = root / "scoop-install"
            calls = []
            def command(command, environment):
                calls.append(command)
                source = command[-1]
                if "scoop install " in source:
                    prefix.mkdir()
                    raise RuntimeError("post-install failure")
                if "scoop uninstall litex-package-smoke" in source:
                    shutil.rmtree(prefix)
                return ""
            server = Mock(server_port=1234)
            probes = [
                subprocess.CompletedProcess([], 1, "", ""),
                subprocess.CompletedProcess([], 0, str(prefix), ""),
            ]
            with patch.object(sys, "argv", ["smoke", "--manager", "scoop", "--archive", str(archive), "--version", "1.0.6-beta"]), \
                    patch.object(package_manager_smoke, "ThreadingHTTPServer", return_value=server), \
                    patch.object(package_manager_smoke.subprocess, "run", side_effect=probes), \
                    patch.object(package_manager_smoke, "run", side_effect=command):
                with self.assertRaisesRegex(RuntimeError, "post-install failure"):
                    package_manager_smoke.main()
            self.assertTrue(any("scoop uninstall litex-package-smoke" in call[-1] for call in calls))
            self.assertFalse(prefix.exists())
            server.server_close.assert_called_once()

    def test_homebrew_partial_install_is_cleaned_and_formula_restored(self) -> None:
        with tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
            root = Path(temporary_directory)
            archive = root / "archive.tar.gz"
            archive.write_bytes(b"package")
            tap = root / "tap"
            tap.mkdir()
            formula = tap / "litex.rb"
            original = b"original formula\n"
            formula.write_bytes(original)
            calls = []
            def command(command, environment):
                calls.append(command)
                if command[:2] == ["brew", "--repository"]:
                    return str(tap)
                if command[:2] == ["brew", "install"]:
                    raise RuntimeError("post-install failure")
                return ""
            server = Mock(server_port=1234)
            probes = [
                subprocess.CompletedProcess([], 1, "", ""),
                subprocess.CompletedProcess([], 0, "litex 1.0.6-beta\n", ""),
            ]
            with patch.object(sys, "argv", ["smoke", "--manager", "homebrew", "--archive", str(archive), "--version", "1.0.6-beta"]), \
                    patch.object(package_manager_smoke, "ThreadingHTTPServer", return_value=server), \
                    patch.object(package_manager_smoke.subprocess, "run", side_effect=probes), \
                    patch.object(package_manager_smoke, "run", side_effect=command):
                with self.assertRaisesRegex(RuntimeError, "post-install failure"):
                    package_manager_smoke.main()
            self.assertIn(["brew", "uninstall", "--force", "litexlang/tap/litex"], calls)
            self.assertEqual(formula.read_bytes(), original)
            server.shutdown.assert_called_once()
            server.server_close.assert_called_once()

    def test_native_package_manager_checks_use_the_release_formula_and_manifest(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text()
        url = "http://127.0.0.1:1234/litex.zip"
        digest = "a" * 64
        formula = package_manager_smoke.homebrew_formula(workflow, url, "1.0.6-beta", digest)
        self.assertIn('(bin/"std").install Dir["std/*"]', formula)
        self.assertIn('ENV.delete("LITEX_STD_PATH")', formula)
        self.assertIn(url, formula)
        self.assertNotIn("PLACEHOLDER", formula)
        self.assertNotIn("SHA_LINUX", formula)
        manifest = package_manager_smoke.scoop_manifest(workflow, url, "1.0.6-beta", digest)
        self.assertEqual(manifest["architecture"]["64bit"], {"url": url, "hash": digest})
        self.assertEqual(manifest["bin"], [["litex.exe", "litex"]])
        self.assertEqual(manifest["version"], "1.0.6-beta")

    def test_all_std_package_channels_exclude_local_cache_and_drafts(self) -> None:
        with tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
            root = Path(temporary_directory)
            std = root / "std"
            (std / "basics").mkdir(parents=True)
            (std / "basics/litex.config").write_text('[export]\nmain = "./main.lit"\n')
            (std / "basics/main.lit").write_text('let version = 1\n')
            for name in ["__litex_knowledge_base__/cache.json", ".draft/probe.lit", "todo.md", ".DS_Store"]:
                file = std / "basics" / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text("local-only")
            output = root / "package/std"
            package_std.copy_std(std, output)
            names = {p.relative_to(output).as_posix() for p in output.rglob("*") if p.is_file()}
            self.assertEqual(names, {"basics/litex.config", "basics/main.lit"})
            self.assertEqual(generate_wix_std.collect_files(std), package_std.source_files(std))

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

    def test_archive_smoke_discovers_shipped_std_from_an_external_project(self) -> None:
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
            self.assertNotIn("LITEX_STD_PATH", smoke_env)
            smoke_project = run.call_args_list[1].kwargs["cwd"]
            self.assertEqual(smoke_project, root / "external-project")
            self.assertFalse((smoke_project / "std").exists())
            self.assertIn("-strict", run.call_args_list[1].args[0])
            self.assertIn("basics::main::litex_distribution_probe = 1", (smoke_project / "smoke.lit").read_text())
            self.assertEqual((root / "extracted/std/basics/main.lit").read_bytes(), b"")

    def test_installed_probe_restores_std_on_verification_failure(self) -> None:
        with tempfile.TemporaryDirectory(dir=PRIVATE_ROOT) as temporary_directory:
            root = Path(temporary_directory)
            install = root / "install"
            basics = install / "std/basics"
            basics.mkdir(parents=True)
            binary = install / "litex"
            binary.write_text("binary")
            (basics / "litex.config").write_text('[export]\nmain = "./main.lit"\n')
            original = b"# intentionally empty\r\n"
            (basics / "main.lit").write_bytes(original)
            responses = [
                subprocess.CompletedProcess([], 0, "Litex 1.0.6-beta\n"),
                subprocess.CompletedProcess([], 1, '{"kind":"run","success":false}'),
            ]
            with patch.object(preflight.subprocess, "run", side_effect=responses):
                with self.assertRaises(preflight.PreflightError):
                    preflight.check_installed_binary(root, binary, install / "std", "1.0.6-beta")
            self.assertEqual((basics / "main.lit").read_bytes(), original)

    def test_msi_is_a_required_release_asset(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text()
        msi = workflow.split("  package-msi:\n", 1)[1].split("  release:\n", 1)[0]
        release = workflow.split("  release:\n", 1)[1].split("  publish-crates-io:\n", 1)[0]
        self.assertNotIn("continue-on-error:", msi)
        self.assertIn("needs: [validate, build, package-deb, package-msi]", release)
        self.assertIn("name: msi", release)
        self.assertIn("artifacts/*.msi", release)
        self.assertIn("fail_on_unmatched_files: true", release)
        self.assertIn("--installed-binary $binary", msi)
        self.assertNotIn("$env:LITEX_STD_PATH =", msi)

    def test_manual_validation_cannot_publish_and_both_linux_architectures_execute(self) -> None:
        workflow = (REPOSITORY_ROOT / ".github/workflows/deploy.yml").read_text()
        self.assertIn("workflow_dispatch:", workflow)
        for name in ["release", "publish-docker"]:
            job = workflow.split(f"  {name}:\n", 1)[1].split("\n  #", 1)[0]
            self.assertIn("if: github.event_name == 'push'", job)
        for name in ["publish-crates-io", "publish-homebrew", "publish-scoop", "deploy-web-server"]:
            job = workflow.split(f"  {name}:\n", 1)[1].split("\n  #", 1)[0]
            needs = next(line for line in job.splitlines() if line.startswith("    needs:"))
            self.assertIn("release", needs)
        self.assertIn("runner: ubuntu-22.04-arm", workflow)
        self.assertNotIn("cross build", workflow)
        self.assertIn("--test installed_std_cli", workflow)
        self.assertIn("Smoke test .deb (native)", workflow)

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
        self.assertIn("--installed-binary /usr/local/bin/litex --std /usr/share/litex/std", workflow)
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
