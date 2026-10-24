#!/usr/bin/env python3
"""Measure identical Lean goals with numeric bridge controls, after imports."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import statistics
import subprocess


BENCH = Path(__file__).resolve().parents[1]
ROOT = BENCH.parents[1]
ADAPTER = ROOT / "showcases/litex_to_lean_adapter"
WORK = ROOT / "tmp/2026-10-24/type-bridge-experiment"

HEADER = """import Mathlib
import Lean
open Lean Elab Command
set_option Elab.async false
set_option debug.skipKernelTC false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
"""

TIMER = r"""
open Lean Elab Command Meta

partial def bridgeExprNodes : Expr → Nat
  | .app f a => 1 + bridgeExprNodes f + bridgeExprNodes a
  | .lam _ t b _ | .forallE _ t b _ => 1 + bridgeExprNodes t + bridgeExprNodes b
  | .letE _ t v b _ => 1 + bridgeExprNodes t + bridgeExprNodes v + bridgeExprNodes b
  | .mdata _ b | .proj _ _ b => 1 + bridgeExprNodes b
  | _ => 1

elab "#bridge_probe " label:str " : " ty:term " := " proof:term : command => do
  let before ← get
  let start ← IO.monoNanosNow
  let (type, value, targetEnd, proofEnd) ← liftTermElabM do
    let type ← Term.elabType ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let targetEnd ← IO.monoNanosNow
    let value ← Term.elabTermEnsuringType proof (some type)
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then
      throwError "Probe left open variables"
    let proofEnd ← IO.monoNanosNow
    pure (type, value, targetEnd, proofEnd)
  if (← get).messages.hasErrors then
    throwError "Probe elaboration reported errors"
  let elaborationEnd ← IO.monoNanosNow
  let decl := Declaration.thmDecl {
    name := `TypeBridgeCheckedSample
    levelParams := []
    type := type
    value := value
  }
  match (← getEnv).addDeclCore 0 decl none true with
  | .error ex => throwKernelException ex
  | .ok _ => pure ()
  let kernelEnd ← IO.monoNanosNow
  IO.println s!"BRIDGE,{label.getString},{targetEnd-start},{proofEnd-targetEnd},{elaborationEnd-proofEnd},{kernelEnd-elaborationEnd},{kernelEnd-start},{bridgeExprNodes value},{hash value}"
  set before

elab "#bridge_kernel_negative" : command => do
  let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let bad := Declaration.thmDecl {
    name := `TypeBridgeRejectedSample
    levelParams := []
    type := type
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)
  }
  match (← getEnv).addDeclCore 0 bad none true with
  | .error _ => IO.println "KERNEL_NEGATIVE_OK"
  | .ok _ => throwError "Kernel accepted a false equality"

#bridge_kernel_negative
"""


def run(cmd, *, cwd=ROOT, env=None, timeout=300):
    result = subprocess.run(
        [str(x) for x in cmd], cwd=cwd, env=env,
        capture_output=True, text=True, timeout=timeout,
    )
    if result.returncode:
        raise RuntimeError(
            f"Command failed ({result.returncode}): {cmd}\n"
            + result.stdout[-6000:] + result.stderr[-3000:]
        )
    return result.stdout


def lean_environment():
    env = dict(os.environ)
    env["LEAN_PATH"] = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ADAPTER).strip()
    prefix = run(["lake", "env", "lean", "--print-prefix"], cwd=ADAPTER).strip()
    return Path(prefix) / "bin/lean", env


def variants(cases):
    return [(case, method, proof) for case in cases for method, proof in case["methods"].items()]


def validate(cases, lean, env):
    lines = [HEADER]
    names = []
    for case, method, proof in variants(cases):
        name = f"checked_{case['id']}_{method}"
        names.append(name)
        lines.append(f"theorem {name} : {case['statement']} := {proof}\n")
    lines.extend(f"#print axioms {name}" for name in names)
    lines.append("""run_cmd do
  let env ← getEnv
  let some (.thmInfo explicit) := env.find? `checked_cast_annotations_explicit
    | throwError "Missing explicit annotation theorem"
  let some (.thmInfo inferred) := env.find? `checked_cast_annotations_inferred
    | throwError "Missing inferred annotation theorem"
  IO.println s!"ANNOTATION_EXPR_EQUAL,{explicit.value == inferred.value}"
""")
    source = WORK / "Validate.lean"
    source.write_text("\n".join(lines) + "\n")
    output = run([lean, source], cwd=ADAPTER, env=env)
    if "sorryAx" in output or "uses `sorry`" in output:
        raise RuntimeError("Ordinary validation used sorry")
    return {"ordinary_lean_theorems": len(names), "exit": 0, "axioms_output": output,
            "annotation_proofs_identical_expr": "ANNOTATION_EXPR_EQUAL,true" in output}


def measure_lean(cases, lean, env, process, reps):
    lines = [HEADER, TIMER]
    items = variants(cases)
    rng = random.Random(20261024 + process)
    for rep in range(-2, reps):
        order = list(items)
        rng.shuffle(order)
        for case, method, proof in order:
            label = f"{case['id']}__{method}__{rep}"
            lines.append(f'#bridge_probe "{label}" : {case["statement"]} := {proof}\n')
    source = WORK / f"Measure-{process}.lean"
    source.write_text("\n".join(lines) + "\n")
    output = run([lean, source], cwd=ADAPTER, env=env)
    if output.count("KERNEL_NEGATIVE_OK") != 1:
        raise RuntimeError("Missing kernel rejection control")
    rows = []
    for line in output.splitlines():
        if not line.startswith("BRIDGE,"):
            continue
        _, label, *values = line.split(",")
        case, method, rep = label.split("__")
        nums = [int(v) for v in values]
        if len(nums) != 7 or sum(nums[:4]) != nums[4]:
            raise RuntimeError(f"Invalid phase accounting: {line}")
        rows.append({
            "system": "lean", "case": case, "method": method,
            "process": process, "rep": int(rep),
            **dict(zip(
                ["target_ns", "proof_ns", "finalization_ns", "kernel_ns", "total_ns", "proof_tree_nodes", "proof_hash"],
                nums,
            )),
        })
    if len(rows) != len(items) * (reps + 2):
        raise RuntimeError("Missing Lean timing samples")
    return rows


def build_litex(cases, reps):
    selected = [c for c in cases if c.get("litex")]
    rows = ",\n".join(
        f'({json.dumps(c["id"])},{json.dumps(c["litex"])})' for c in selected
    )
    rust = """use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
use std::time::Instant;
fn main() {
let cases = &[CASES];
for rep in -2i32..REPS {
    for (id, source) in cases {
        let mut runtime = Runtime::new(LaunchCommand::Repl { strict: true, language: OutputLanguage::English });
        let start = Instant::now();
        let result = runtime.run_litex_code(source).unwrap();
        let ns = start.elapsed().as_nanos();
        assert!(result.success && result.session_error.is_none() && result.input_error.is_none());
        println!("LITEX,{},{},{}", id, rep, ns);
    }
}
}
""".replace("CASES", rows).replace("REPS", str(reps))
    source = WORK / "Loaded.rs"
    source.write_text(rust)
    executable = WORK / "loaded-litex"
    run(["rustc", "--edition=2021", "-O", source,
         "--extern", f"litex={ROOT / 'target/release/liblitex.rlib'}",
         "-L", f"dependency={ROOT / 'target/release/deps'}", "-o", executable])
    return executable, len(selected)


def measure_litex(executable, expected, process, reps):
    rows = []
    for line in run([executable]).splitlines():
        _, case, rep, ns = line.split(",")
        rows.append({"system": "litex", "case": case, "process": process,
                     "rep": int(rep), "total_ns": int(ns)})
    if len(rows) != expected * (reps + 2):
        raise RuntimeError("Missing Litex timing samples")
    return rows


def summarize(rows):
    groups = {}
    for row in rows:
        if row["rep"] < 0:
            continue
        key = "/".join([row["system"], row["case"]] + ([row["method"]] if "method" in row else []))
        groups.setdefault(key, []).append(row)
    summary = {}
    for key, values in groups.items():
        metrics = [name for name in values[0] if name.endswith("_ns")]
        record = {"n": len(values)}
        for name in metrics:
            samples = [v[name] / 1e6 for v in values]
            median = statistics.median(samples)
            record[name.removesuffix("_ns") + "_ms"] = {
                "median": median, "min": min(samples), "max": max(samples),
                "mad": statistics.median(abs(v - median) for v in samples),
            }
        if "proof_hash" in values[0]:
            record["proof_hashes"] = sorted({v["proof_hash"] for v in values})
            record["proof_tree_nodes"] = sorted({v["proof_tree_nodes"] for v in values})
        summary[key] = record
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", type=Path, default=BENCH / "cases/type-bridge.json")
    parser.add_argument("--reps", type=int, default=11)
    parser.add_argument("--processes", type=int, default=3)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=BENCH / "results")
    args = parser.parse_args()
    if args.reps < 1 or args.processes < 1:
        parser.error("Repetitions and processes must be positive")
    WORK.mkdir(parents=True, exist_ok=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    cases = json.loads(args.cases.read_text())
    lean, env = lean_environment()
    validation = validate(cases, lean, env)
    (args.output_dir / "type-bridge-validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    print(f"Ordinary Lean validation: {validation['ordinary_lean_theorems']} theorems", flush=True)
    if args.validate_only:
        return
    executable, litex_cases = build_litex(cases, args.reps)
    raw = []
    for process in range(args.processes):
        raw.extend(measure_lean(cases, lean, env, process, args.reps))
        raw.extend(measure_litex(executable, litex_cases, process, args.reps))
        print(f"Measured process {process + 1}/{args.processes}", flush=True)
    environment = {
        "lean": run([lean, "--version"], cwd=ADAPTER, env=env).strip(),
        "litex": run([ROOT / "target/release/litex", "-version"]).strip(),
        "platform": run(["uname", "-sm"]).strip(),
        "date": run(["date", "+%Y-%m-%dT%H:%M:%S%z"]).strip(),
        "reps": args.reps, "processes": args.processes, "warmup_per_variant": 2,
        "imports": ["Mathlib", "Lean"],
        "startup_and_imports_timed": False,
        "parser_timed": {"lean": False, "litex": True},
        "sample_order_seed_base": 20261024,
        "lean_kernel_entrypoint": "Lean.Environment.addDeclCore 0 declaration none true",
        "phase_note": "Proof elaboration may also check generated auxiliary declarations. The final kernel phase is not a profiler of every kernel call.",
        "git_head": run(["git", "rev-parse", "HEAD"]).strip(),
        "rustc": run(["rustc", "--version"]).strip(),
        "phase_source_sha256": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(WORK.glob("Measure-*.lean"))
        },
        "sha256": {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [args.cases.resolve(), Path(__file__).resolve(), ROOT / "target/release/litex", ROOT / "target/release/liblitex.rlib"]
        },
    }
    for name, value in [("raw", raw), ("summary", summarize(raw)), ("environment", environment)]:
        (args.output_dir / f"type-bridge-{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    validation["kernel_negative_controls_passed"] = args.processes
    validation["measured_lean_samples_including_warmup"] = sum(r["system"] == "lean" for r in raw)
    validation["all_phase_totals_checked"] = True
    (args.output_dir / "type-bridge-validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    print(json.dumps({key: value["total_ms"]["median"] for key, value in summarize(raw).items()}, indent=2), flush=True)


if __name__ == "__main__":
    main()
