#!/usr/bin/env python3
"""Reproduce the Litex / Lean checking-time measurements published here.

Usage (from the repository root):

    cargo build --release
    python3 examples/litex_vs_lean_speed/harness/bench.py all

`validate` writes per-case sources, checks every Litex source with the release
binary, and compiles every Lean route in one file with `#print axioms`.
`measure` reuses those sources and records warm samples in three processes for
each side. Results land in `results/`.

Each side is timed on its own checking path:

* Litex: a fresh strict `Runtime` per sample; the interval covers tokenizing,
  parsing, well-definedness, verification, storing and evidence building.
  Runtime construction is outside the interval. The binary is a release build
  of this repository.
* Lean: a `#probe` command wraps `elabCommand` with a nanosecond clock, with
  `Elab.async=false` so elaboration and kernel checking are synchronous. The
  interval excludes parsing of the command and `import Mathlib`.

Neither side includes process startup, imports, or JSON/console rendering.
These are concrete comparisons of two checking paths, not a general ranking of
the two languages.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
ROOT = BENCH.parents[1]
CASES_FILE = BENCH / "cases" / "new-round.json"
SOURCES = BENCH / "sources" / "new-round"
RESULTS = BENCH / "results"
WORK = ROOT / "tmp" / "litex_vs_lean_speed"
ADAPTER = ROOT / "showcases" / "litex_to_lean_adapter"

LITEX = ROOT / "target" / "release" / "litex"
RLIB = ROOT / "target" / "release" / "liblitex.rlib"

LEAN_HEADER = """import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
"""

LEAN_TIMER = """open Lean Elab Command in
elab "#probe " label:str cmd:command : command => do
  let before ← get
  let start ← IO.monoNanosNow
  let mut success := true
  try
    elabCommand cmd
    if (← get).messages.hasErrors then
      success := false
  catch ex =>
    success := false
    IO.println s!"EXCEPTION,{label.getString},{← ex.toMessageData.toString}"
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"PROBE,{label.getString},{success},{elapsed}"
  set before
"""

LITEX_REPS = 30
LEAN_REPS = 7
PROCESSES = 3


def load_cases():
    return json.loads(CASES_FILE.read_text())


def lean_bin():
    env = os.environ.get("LEAN")
    if env:
        return Path(env)
    candidates = sorted(
        (Path.home() / ".elan" / "toolchains").glob("leanprover--lean4---*/bin/lean")
    )
    if candidates:
        return candidates[0]
    found = shutil.which("lean")
    if not found:
        sys.exit("no Lean binary found; set LEAN=/path/to/lean")
    return Path(found)


def lean_path():
    if os.environ.get("LEAN_PATH"):
        return os.environ["LEAN_PATH"]
    if not ADAPTER.exists():
        sys.exit("cannot locate showcases/litex_to_lean_adapter to read LEAN_PATH")
    out = subprocess.run(
        ["lake", "env", "bash", "-c", "printenv LEAN_PATH"],
        cwd=ADAPTER,
        capture_output=True,
        text=True,
    )
    if out.returncode != 0 or not out.stdout.strip():
        sys.exit("lake could not report LEAN_PATH; run `lake build` in the adapter first")
    return out.stdout.strip()


def call(cmd, cwd=None, timeout=900, env=None):
    p = subprocess.run(
        [str(x) for x in cmd],
        cwd=str(cwd or ROOT),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return p


def slug(case_id, method=None):
    return case_id if method is None else f"{case_id}__{method}"


def write_sources(cases):
    SOURCES.mkdir(parents=True, exist_ok=True)
    written = []
    for c in cases:
        lit = SOURCES / f"{c['id']}.lit"
        lit.write_text(c["litex"].rstrip("\n") + "\n")
        written.append(lit)
        for method, proof in c["methods"].items():
            lean = SOURCES / f"{slug(c['id'], method)}.lean"
            lean.write_text(
                "import Mathlib\n\n"
                f"example : {c['lean']} := {proof}\n"
            )
            written.append(lean)
    return written


def validate_litex(cases):
    rows = []
    for c in cases:
        src = SOURCES / f"{c['id']}.lit"
        p = call([LITEX, "-f", src])
        verdict = "unparsed"
        try:
            d = json.loads(p.stdout)
            verdict = d.get("run_result", "unknown")
            if verdict != "success":
                verdict = f"{verdict}: {d.get('errors')}"
        except json.JSONDecodeError:
            verdict = (p.stdout + p.stderr).strip()[:400]
        rows.append({"case": c["id"], "litex": verdict})
    return rows


def validate_lean(cases):
    lines = [LEAN_HEADER]
    names = []
    for c in cases:
        for method, proof in c["methods"].items():
            name = f"validated_{c['id']}_{method}"
            names.append(name)
            lines.append(f"theorem {name} : {c['lean']} := {proof}\n")
    for name in names:
        lines.append(f"#print axioms {name}\n")
    src = SOURCES / "Validate.lean"
    src.write_text("\n".join(lines))
    env = dict(os.environ, LEAN_PATH=lean_path())
    p = call([lean_bin(), src], cwd=WORK, env=env)
    bad = "sorryAx" in p.stdout
    return {
        "file": "sources/new-round/Validate.lean",
        "exit": p.returncode,
        "sorry": bad,
        "stderr": p.stderr[-2000:],
        "stdout_tail": p.stdout[-2000:],
    }


def build_litex_harness(cases):
    rust = [
        "use litex::launch_command::{LaunchCommand,OutputLanguage};",
        "use litex::runtime::Runtime;",
        "use std::time::Instant;",
        "fn main(){",
        "let cases=&[",
    ]
    for c in cases:
        rust.append(f"({json.dumps(c['id'])},{json.dumps(c['litex'])}),")
    rust.append("];")
    rust.append(
        f"for (label,source) in cases {{\n for rep in 0..{LITEX_REPS} {{\n"
        "  let mut runtime=Runtime::new(LaunchCommand::Repl{strict:true,language:OutputLanguage::English});\n"
        "  let start=Instant::now();\n"
        "  let result=runtime.run_litex_code(source).unwrap();\n"
        "  let elapsed=start.elapsed().as_nanos();\n"
        "  assert!(result.success && result.session_error.is_none() && result.input_error.is_none());\n"
        '  println!("BENCH,{},{},{}",label,rep,elapsed);\n }}\n}\n'
    )
    rs = WORK / "Loaded.rs"
    rs.write_text("\n".join(rust))
    out = WORK / "loaded-litex"
    p = call(
        [
            "rustc",
            "--edition=2021",
            "-O",
            rs,
            "--extern",
            f"litex={RLIB}",
            "-L",
            f"dependency={ROOT / 'target' / 'release' / 'deps'}",
            "-o",
            out,
        ]
    )
    if p.returncode != 0:
        sys.exit("rustc failed:\n" + p.stderr[-4000:])
    return out


def measure_litex(cases):
    exe = build_litex_harness(cases)
    rows = []
    per_proc = {}
    for proc in range(PROCESSES):
        p = call([exe])
        if p.returncode != 0:
            sys.exit("litex harness failed:\n" + p.stderr[-4000:])
        for case_id, rep, ns in re.findall(r"BENCH,(\w+),(\d+),(\d+)", p.stdout):
            rows.append(
                {
                    "system": "litex",
                    "case": case_id,
                    "process": proc,
                    "rep": int(rep),
                    "ms": int(ns) / 1e6,
                }
            )
        per_proc[proc] = len([r for r in rows if r["process"] == proc])
    expected = len(cases) * LITEX_REPS
    assert all(v == expected for v in per_proc.values()), (per_proc, expected)
    return rows


def measure_lean(cases):
    lines = [LEAN_HEADER, LEAN_TIMER]
    for c in cases:
        for method, proof in c["methods"].items():
            stmt = c["lean"]
            lines.append(
                f'#probe "{slug(c["id"], method)}__first" '
                f"theorem initial_{c['id']}_{method} : {stmt} := {proof}\n"
            )
        for method, proof in c["methods"].items():
            for rep in range(LEAN_REPS):
                lines.append(
                    f'#probe "{slug(c["id"], method)}" '
                    f"theorem sample_{c['id']}_{method}_{rep} : {c['lean']} := {proof}\n"
                )
    src = SOURCES / "Repeat.lean"
    src.write_text("\n".join(lines))
    env = dict(os.environ, LEAN_PATH=lean_path())
    rows = []
    for proc in range(PROCESSES):
        p = call([lean_bin(), src], cwd=WORK, env=env)
        if p.returncode != 0:
            sys.exit("Lean harness failed:\n" + (p.stderr + p.stdout)[-6000:])
        for label, ok, ns in re.findall(r"PROBE,(\w+),(true|false),(\d+)", p.stdout):
            if not ok:
                sys.exit(f"Lean route {label} did not succeed")
            if label.endswith("__first"):
                kind = "first"
                label = label[: -len("__first")]
            else:
                kind = "warm"
            rows.append(
                {
                    "system": "lean",
                    "case": label,
                    "process": proc,
                    "rep": kind,
                    "ms": int(ns) / 1e6,
                }
            )
    return rows


def summarise(rows):
    groups = {}
    for r in rows:
        if r["rep"] == "first":
            continue
        groups.setdefault((r["system"], r["case"]), []).append(r["ms"])
    return {
        f"{system}/{case}": {
            "n": len(vals),
            "median_ms": statistics.median(vals),
            "min_ms": min(vals),
            "max_ms": max(vals),
        }
        for (system, case), vals in groups.items()
    }


def markdown(cases, summary):
    """Summary table; full per-case sources live next to it as files."""
    out = [
        "| 领域 | 用例 | Litex (ms) | Lean (ms) | Lean÷Litex | Lean 最快路线 | 源码 |",
        "| --- | --- | ---: | ---: | ---: | --- | --- |",
    ]
    for c in cases:
        lit = summary.get(f"litex/{c['id']}")
        best = None
        primary = c.get("primary_method")
        if primary in c["methods"] and f"lean/{slug(c['id'], primary)}" in summary:
            best = (primary, summary[f"lean/{slug(c['id'], primary)}"])
        else:
            for method in c["methods"]:
                s = summary.get(f"lean/{slug(c['id'], method)}")
                if s and (best is None or s["median_ms"] < best[1]["median_ms"]):
                    best = (method, s)
        lit_ms = lit["median_ms"] if lit else float("nan")
        lean_ms = best[1]["median_ms"] if best else float("nan")
        ratio = lean_ms / lit_ms if lit and best else float("nan")
        out.append(
            f"| {c['domain']} | {c['label']} | {lit_ms:.3f} | {lean_ms:.3f} "
            f"| **{ratio:.2f}×** | `{best[0]}` "
            f"| [litex](../sources/new-round/{c['id']}.lit) · "
            f"[lean](../sources/new-round/{slug(c['id'], best[0])}.lean) |"
        )
    return "\n".join(out)


def environment():
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None

    def version(cmd, cwd=None, env=None):
        try:
            p = call(cmd, cwd=cwd, env=env)
            return (p.stdout + p.stderr).strip()
        except Exception as ex:  # pragma: no cover - diagnostics only
            return f"unavailable: {ex}"

    return {
        "date": subprocess.check_output(
            ["date", "+%Y-%m-%d %H:%M %Z"], text=True
        ).strip(),
        "platform": subprocess.check_output(["uname", "-sm"], text=True).strip(),
        "litex": version([LITEX, "-version"]),
        "lean": version([lean_bin(), "--version"]),
        "rustc": version(["rustc", "--version"]),
        "golitex_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "sha256": {"litex": sha(LITEX), "liblitex.rlib": sha(RLIB)},
        "reps": {
            "litex_warm_per_process": LITEX_REPS,
            "lean_warm_per_process": LEAN_REPS,
            "processes": PROCESSES,
        },
    }


def main():
    global CASES_FILE, SOURCES
    parser = argparse.ArgumentParser()
    parser.add_argument("stage", choices=["validate", "measure", "all"])
    parser.add_argument(
        "--cases",
        default=None,
        help="path to a cases JSON file (default: cases/new-round.json)",
    )
    args = parser.parse_args()
    CASES_FILE = Path(args.cases) if args.cases else BENCH / "cases" / "new-round.json"
    SOURCES = BENCH / "sources" / CASES_FILE.stem

    cases = json.loads(CASES_FILE.read_text())
    WORK.mkdir(parents=True, exist_ok=True)
    RESULTS.mkdir(parents=True, exist_ok=True)
    write_sources(cases)

    if args.stage in ("validate", "all"):
        lit = validate_litex(cases)
        lean = validate_lean(cases)
        report = {"litex": lit, "lean": lean}
        (RESULTS / f"{CASES_FILE.stem}-validation.json").write_text(
            json.dumps(report, ensure_ascii=False, indent=2)
        )
        bad = [r for r in lit if r["litex"] != "success"]
        if bad:
            sys.exit(f"Litex validation failed: {bad}")
        if lean["exit"] != 0 or lean["sorry"]:
            sys.exit(f"Lean validation failed: {lean}")
        print(f"validation ok: {len(cases)} Litex sources, "
              f"{sum(len(c['methods']) for c in cases)} Lean routes")

    if args.stage in ("measure", "all"):
        rows = measure_litex(cases) + measure_lean(cases)
        summary = summarise(rows)
        (RESULTS / f"{CASES_FILE.stem}-raw.json").write_text(
            json.dumps(rows, indent=2)
        )
        (RESULTS / f"{CASES_FILE.stem}-summary.json").write_text(
            json.dumps(summary, ensure_ascii=False, indent=2)
        )
        (RESULTS / f"{CASES_FILE.stem}.md").write_text(markdown(cases, summary) + "\n")
        (RESULTS / "environment.json").write_text(
            json.dumps(environment(), ensure_ascii=False, indent=2)
        )
        print(markdown(cases, summary))


if __name__ == "__main__":
    main()
