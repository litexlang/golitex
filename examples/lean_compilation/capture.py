#!/usr/bin/env python3
"""Refresh this demo only after source, same-result replay and Lean all pass."""
import hashlib
import json
from datetime import date
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = HERE / "source.lit"
LAKE = ROOT / "showcases/litex_to_lean_adapter"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def core_digest():
    value = hashlib.sha256()
    for path in sorted((ROOT / "lean").glob("Litex*.lean")) + sorted((ROOT / "lean/Litex").rglob("*.lean")):
        value.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes())
    return value.hexdigest()


def main():
    subprocess.run(["cargo", "build", "--release", "--locked"], cwd=ROOT, check=True)
    source = str(SOURCE.relative_to(ROOT))
    binary = ROOT / "target/release/litex"
    cli = subprocess.run([str(binary), "-strict", "-lean", "-f", source],
                         cwd=ROOT, check=True, capture_output=True).stdout
    namespace = next(line.split(" ", 1)[1] for line in cli.decode().splitlines()
                     if line.startswith("namespace "))
    namespace = namespace.removeprefix("LitexCompiled.")
    library = ROOT / "target/release/liblitex.rlib"
    with tempfile.TemporaryDirectory(prefix="litex-demo-capture-") as temporary:
        work = Path(temporary)
        helper = work / "capture"
        subprocess.run(["rustc", "--edition=2021", str(HERE / "capture.rs"),
                        "--extern", f"litex={library}", "-L",
                        f"dependency={ROOT / 'target/release/deps'}", "-o", str(helper)], check=True)
        subprocess.run([str(helper), source, namespace, str(work)], cwd=ROOT, check=True)
        assert (work / "generated.lean").read_bytes() == cli, "same-result output differs from CLI"
        subprocess.run(["lake", "build", "Litex"], cwd=LAKE, check=True)
        subprocess.run(["lake", "env", "lean", str(work / "generated.lean")],
                       cwd=LAKE, check=True)
        detail = (work / "detailed.json").read_bytes()
    (HERE / "Generated.lean").write_bytes(cli)
    (HERE / "trace.detailed.json").write_bytes(detail)
    evidence = {
        "date": date.today().isoformat(), "source": source,
        "generated": str((HERE / "Generated.lean").relative_to(ROOT)),
        "strict": True, "source_success": True, "same_result_compiled": True,
        "canonical_byte_match": True, "lean_kernel_checked": True,
        "core_freshly_checked": True,
        "lean_version": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=LAKE, text=True).strip(),
        "mathlib_revision": next(p["rev"] for p in json.loads((LAKE / "lake-manifest.json").read_text())["packages"]
                                 if p["name"] == "mathlib"),
        "source_sha256": digest(SOURCE), "generated_sha256": digest(HERE / "Generated.lean"),
        "core_sha256": digest(ROOT / "lean/Litex.lean"), "core_tree_sha256": core_digest(),
        "binary_sha256": digest(binary), "rust_library_sha256": digest(library),
        "detailed_sha256": digest(HERE / "trace.detailed.json"),
    }
    (HERE / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    subprocess.run(["python3", str(HERE / "build.py")], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
