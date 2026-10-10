#!/usr/bin/env python3
"""Install this run's archive through Homebrew/Scoop, then check real std use.

Run on a disposable native CI runner with the package manager already installed.
No package or manifest is published. A loopback server supplies the local archive.
"""

import argparse
from functools import partial
import hashlib
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
from urllib.parse import quote

from preflight import check_installed_binary


def homebrew_formula(workflow: str, url: str, version: str, digest: str) -> str:
    template = workflow.split("<< 'FORMULA'\n", 1)[1].split("\n          FORMULA", 1)[0]
    template = "\n".join(line[10:] for line in template.splitlines()) + "\n"
    template = re.sub(r'url "[^"]+"', 'url ' + json.dumps(url), template)
    template = template.replace("VERSION_PLACEHOLDER", version)
    for placeholder in ["SHA_DARWIN_ARM64", "SHA_LINUX_AMD64", "SHA_LINUX_ARM64"]:
        template = template.replace(placeholder, digest)
    return template


def scoop_manifest(workflow: str, url: str, version: str, digest: str) -> dict:
    template = workflow.split("cat > scoop-litex/litex.json << EOF\n", 1)[1].split("\n          EOF", 1)[0]
    template = template.replace("${VERSION}", version)
    template = template.replace("${{ steps.sha.outputs.windows_amd64 }}", digest)
    template = template.replace("\\$version", "$version")
    manifest = json.loads(template)
    manifest["architecture"]["64bit"]["url"] = url
    return manifest


def run(command: list[str], environment: dict[str, str]) -> str:
    result = subprocess.run(command, env=environment, text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError(f"{command}:\n{result.stdout}{result.stderr}")
    return result.stdout.strip()


def powershell(command: str) -> list[str]:
    return ["pwsh", "-NoProfile", "-Command", "$ErrorActionPreference = 'Stop'; " + command + "; if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manager", choices=["homebrew", "scoop"], required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--version", required=True)
    arguments = parser.parse_args()
    if not re.fullmatch(r"[0-9A-Za-z.+-]+", arguments.version):
        parser.error("unexpected package version")
    archive = arguments.archive.resolve()
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    repository = Path(__file__).resolve().parents[3]
    workflow = (repository / ".github/workflows/deploy.yml").read_text()
    environment = dict(os.environ)
    environment.pop("LITEX_STD_PATH", None)
    environment["HOMEBREW_NO_AUTO_UPDATE"] = "1"
    environment["HOMEBREW_NO_INSTALL_CLEANUP"] = "1"

    with tempfile.TemporaryDirectory(prefix="litex-package-manager-") as temporary:
        work = Path(temporary)
        served = work / "served"
        served.mkdir()
        shutil.copy2(archive, served / archive.name)
        server = ThreadingHTTPServer(("127.0.0.1", 0), partial(SimpleHTTPRequestHandler, directory=str(served)))
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        url = f"http://127.0.0.1:{server.server_port}/{quote(archive.name)}"
        try:
            if arguments.manager == "homebrew":
                existing = subprocess.run(["brew", "list", "--versions", "litex"], env=environment, text=True, capture_output=True)
                if existing.stdout.strip():
                    raise RuntimeError("refusing to replace a pre-existing Litex installation; use a fresh CI runner")
                run(["brew", "tap", "litexlang/tap", "https://github.com/litexlang/homebrew-tap"], environment)
                tap = Path(run(["brew", "--repository", "litexlang/tap"], environment))
                formula = tap / "litex.rb"
                original = formula.read_bytes()
                attempted = False
                try:
                    formula.write_text(homebrew_formula(workflow, url, arguments.version, digest))
                    attempted = True
                    run(["brew", "install", "--build-from-source", "litexlang/tap/litex"], environment)
                    run(["brew", "test", "litexlang/tap/litex"], environment)
                    prefix = Path(run(["brew", "--prefix", "litexlang/tap/litex"], environment))
                    check_installed_binary(work, prefix / "bin/litex", prefix / "bin/std", arguments.version)
                finally:
                    try:
                        if attempted:
                            current = subprocess.run(
                                ["brew", "list", "--versions", "litexlang/tap/litex"],
                                env=environment, text=True, capture_output=True,
                            )
                            if current.returncode == 0 and current.stdout.strip():
                                run(["brew", "uninstall", "--force", "litexlang/tap/litex"], environment)
                    finally:
                        formula.write_bytes(original)
            else:
                manifest = work / "litex-package-smoke.json"
                manifest.write_text(json.dumps(scoop_manifest(workflow, url, arguments.version, digest)))
                quoted = "'" + str(manifest).replace("'", "''") + "'"
                prefix_command = powershell("scoop prefix litex-package-smoke")
                existing = subprocess.run(prefix_command, env=environment, text=True, capture_output=True)
                if existing.returncode == 0 and existing.stdout.strip() and Path(existing.stdout.strip()).is_dir():
                    raise RuntimeError("refusing to replace a pre-existing Scoop test installation")
                try:
                    run(powershell("scoop install " + quoted), environment)
                    prefix = Path(run(powershell("scoop prefix litex-package-smoke"), environment))
                    check_installed_binary(work, prefix / "litex.exe", prefix / "std", arguments.version)
                finally:
                    current = subprocess.run(prefix_command, env=environment, text=True, capture_output=True)
                    if current.returncode == 0 and current.stdout.strip() and Path(current.stdout.strip()).is_dir():
                        run(powershell("scoop uninstall litex-package-smoke"), environment)
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
    print(f"{arguments.manager} installation and bundled std smoke: PASS")


if __name__ == "__main__":
    main()
