"""Verify imported independence, bases and coordinates, rejection boundaries and std distribution."""

from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / "target/release/litex"
POSITIVES = (
    HERE / "main.lit",
    ROOT / "std/algebra/basis.lit",
    ROOT / "showcases/linear_algebra/linear_algebra.lit",
    HERE / "contracts.lit",
    HERE / "zero_dimensional/main.lit",
    HERE / "negative/context.lit",
)
NEGATIVES = {
    "no_basis_guard": "well_defined",
    "empty_not_basis": "well_defined",
    "wrong_coordinate": "search_proof",
    "index_out_of_range": "well_defined",
    "missing_representation": "premise",
    "missing_independence": "premise",
    "removed_index_out_of_range": "premise",
}


def run(path, *, binary=BINARY, cwd=ROOT, bundled=False):
    env = dict(os.environ)
    env.pop("LITEX_STD_PATH", None)
    if not bundled:
        env["LITEX_STD_PATH"] = str(ROOT / "std")
    result = subprocess.run(
        [str(binary), "-lang", "en", "-strict", "-f", str(path)],
        cwd=cwd, env=env, text=True, capture_output=True, timeout=300,
    )
    output = json.loads(result.stdout)
    assert output["kind"] == "run", output
    assert output["session_terminated"] is False, output
    assert output["termination"] is None, output
    assert output["statement_results"], output
    return result, output


def assert_positive(result, output):
    assert result.returncode == 0, output
    assert output["run_result"] == "success", output
    assert not output["errors"], output
    assert all(s["statement_result"] == "accepted"
               for s in output["statement_results"]), output


def main():
    with ThreadPoolExecutor(max_workers=2) as pool:
        for path, (result, output) in zip(POSITIVES, pool.map(run, POSITIVES)):
            assert_positive(result, output)
            print(f"{path.relative_to(ROOT)}: {len(output['statement_results'])} accepted")
        paths = [HERE / "negative" / f"{name}.lit" for name in NEGATIVES]
        for (name, phase), (result, output) in zip(NEGATIVES.items(), pool.map(run, paths)):
            assert result.returncode == 1, output
            assert output["run_result"] == "failure", output
            statements = output["statement_results"]
            assert all(s["statement_result"] == "accepted" for s in statements[:-1]), output
            assert statements[-1]["statement_result"] == "rejected", output
            assert len(output["errors"]) == 1, output
            error = output["errors"][0]
            assert error["statement_index"] == len(statements)-1, output
            assert error["phase"] == phase, output
            print(f"{name}: final statement rejected at {phase}")

    spec = importlib.util.spec_from_file_location(
        "package_std", ROOT / ".github/scripts/release/package_std.py")
    package_std = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(package_std)
    payload = {"std/"+p.relative_to(ROOT / "std").as_posix()
               for p in package_std.source_files(ROOT / "std")}
    assert {"std/algebra/"+name for name in (
        "group.lit", "field.lit", "vector_space.lit", "finite_span.lit", "basis.lit",
        "litex.config", "README.md", "math_collections.md")}.issubset(payload)
    wix = ET.parse(ROOT / "wix/std.wxs")
    wix_payload = {node.attrib["Source"].replace("\\", "/")
                   for node in wix.findall(".//{http://schemas.microsoft.com/wix/2006/wi}File")}
    assert wix_payload == payload, (wix_payload ^ payload)
    print(f"std package inventory: {len(payload)} distributable files")

    with tempfile.TemporaryDirectory(prefix="litex-algebra-install-") as temporary:
        base = Path(temporary)
        for label, executable_dir, std_dir in (
            ("archive", "archive", "archive/std"),
            ("shared-data", "prefix/bin", "prefix/share/litex/std"),
        ):
            directory = base / executable_dir
            directory.mkdir(parents=True, exist_ok=True)
            binary = directory / BINARY.name
            shutil.copy2(BINARY, binary)
            package_std.copy_std(ROOT / "std", base / std_dir)
            project = base / f"{label}-project"
            project.mkdir()
            for name in ("litex.config", "main.lit", "contracts.lit"):
                shutil.copy2(HERE / name, project / name)
            result, output = run(project / "main.lit", binary=binary, cwd=project, bundled=True)
            assert_positive(result, output)
            print(f"{label}: actual algebra library discovered without a path override")
    print("15 focused basis/coordinate CLI checks and std inventory passed")


if __name__ == "__main__":
    main()
