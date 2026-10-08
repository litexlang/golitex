#!/usr/bin/env python3
"""Check the object interface with cached Mathlib and workspace-local outputs."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, default=root / ".lake/packages")
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    packages = args.packages_dir.resolve()
    manifest = json.loads((root / "lake-manifest.json").read_text())
    expected_revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    actual_revision = subprocess.run(
        ["git", "-C", str(packages / "mathlib"), "rev-parse", "HEAD"],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    if actual_revision != expected_revision:
        raise SystemExit("Mathlib checkout does not match lake-manifest.json")
    version = subprocess.run(
        [args.lean, "--version"], cwd=root, capture_output=True, text=True, check=True,
    ).stdout.strip()
    if "version 4.31.0" not in version:
        raise SystemExit(f"Expected Lean 4.31.0; got {version}")
    libraries = sorted(p for p in packages.glob("*/.lake/build/lib/lean") if p.is_dir())
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib/Data/Complex/Basic.olean").is_file():
        raise SystemExit("Mathlib oleans are missing; initialize the pinned Lake dependencies first")
    output = root / ".lake/build/lib/lean"
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *libraries]))
    sources = [
        "Litex/Semantics.lean", "Litex/Objects.lean", "Litex/Arithmetic.lean",
        "Litex/NumericRules.lean", "Litex/NativeBridge.lean", "Litex.lean",
        "examples/ObjectMvp.lean", "tests/InterfaceChecks.lean",
        "InteropExamples/ExpectedTarget.lean", "InteropExamples/NumericModel.lean",
        "InteropExamples/Adapter.lean", "InteropExamples/Final.lean", "InteropExamples.lean",
        "tests/InteropChecks.lean",
    ]
    audits = {}
    for source in sources:
        destination = output / Path(source).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            [args.lean, "-DwarningAsError=true", "-o", str(destination), source],
            cwd=root, env=env, capture_output=True, text=True,
        )
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
        if source in {"tests/InterfaceChecks.lean", "tests/InteropChecks.lean"}:
            audits[source] = result.stdout
        print(f"PASS {source}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for source, expected_count in [("tests/InterfaceChecks.lean", 8), ("tests/InteropChecks.lean", 11)]:
        audit = audits[source]
        reports = re.findall(r"depends on axioms: \[([^]]*)\]", audit)
        no_axioms = audit.count("does not depend on any axioms")
        if len(reports) + no_axioms != expected_count:
            raise SystemExit(f"Incomplete axiom audit for {source}:\n{audit}")
        for report in reports:
            names = {name.strip() for name in report.split(",") if name.strip()}
            if not names <= allowed:
                raise SystemExit(f"Unexpected project axiom: {report}")
    for source, diagnostic in [
        ("tests/MissingMembership.lean", "type mismatch"),
        ("tests/MissingNonzero.lean", "type mismatch"),
        ("tests/MissingRepresentation.lean", "failed to synthesize"),
        ("tests/InvalidHostEquality.lean", "type mismatch"),
    ]:
        result = subprocess.run(
            [args.lean, "-DwarningAsError=true", source],
            cwd=root, env=env, capture_output=True, text=True,
        )
        if result.returncode == 0 or diagnostic not in (result.stdout + result.stderr).lower():
            raise SystemExit(f"Wrong negative result for {source}:\n{result.stdout}{result.stderr}")
        print(f"PASS expected rejection: {source}")
    consumer = subprocess.run(
        [args.lean, "--stdin"], cwd=root, env=env, capture_output=True, text=True,
        input="import InteropExamples\n#print Adapter.complexAddZero\n"
        "#check NativeConsumer.complexAddZero\n#check NativeConsumer.realAddZero\n",
    )
    if consumer.returncode or "InteropExamples.ExpectedTarget.addZero" not in consumer.stdout:
        raise SystemExit(f"Missing target-proof dependency:\n{consumer.stdout}{consumer.stderr}")
    print("PASS native import and live ExpectedTarget.addZero dependency")
    for source in sorted(root.rglob("*.lean")):
        if ".lake" in source.relative_to(root).parts:
            continue
        if re.search(r"\b(axiom|sorry|admit|sorryAx)\b", source.read_text()):
            raise SystemExit(f"Forbidden proof declaration or placeholder in {source}")
    print("PASS axiom audit (19 declarations; no project axioms or proof holes)")
    print("Concrete numeric interoperability example passed; full Litex model/compiler remain unimplemented.")


if __name__ == "__main__":
    main()
