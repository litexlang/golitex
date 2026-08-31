#!/usr/bin/env python3
"""Compile every registered Lean example into tmp and kernel-check both copies."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = ROOT / "lean/examples"
LEAN_ROOT = ROOT / "lean"
TMP_ROOT = ROOT / "tmp"
COMPILER = ROOT / "target/release/stmt_result_to_lean_compiler"
DEFAULT_REPORT = ROOT / "lean/coverage/example_kernel_matrix.json"
FORBIDDEN_OUTPUT = re.compile(
    r"\b(?:sorry|admit|LitexObject)\b|Litex\.Object|Set\.univ"
)


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_dependency_fingerprint() -> str:
    digest = hashlib.sha256()
    paths = list((LEAN_ROOT / "Litex").rglob("*.lean"))
    paths.extend(
        path
        for path in (
            LEAN_ROOT / "Litex.lean",
            LEAN_ROOT / "lakefile.lean",
            LEAN_ROOT / "lean-toolchain",
        )
        if path.exists()
    )
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def rust_source_fingerprint() -> str:
    digest = hashlib.sha256()
    paths = list((ROOT / "src").rglob("*.rs"))
    paths.extend(path for path in (ROOT / "Cargo.toml", ROOT / "Cargo.lock") if path.exists())
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def example_input_fingerprint(sources: list[Path]) -> str:
    digest = hashlib.sha256()
    paths = [EXAMPLES / "litex.config"]
    paths.extend(sources)
    paths.extend(source.with_suffix(".lean") for source in sources)
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def lean_olean_precondition_errors() -> list[str]:
    pairs = [(LEAN_ROOT / "Litex.lean", LEAN_ROOT / ".lake/build/lib/lean/Litex.olean")]
    for source in sorted((LEAN_ROOT / "Litex").rglob("*.lean")):
        relative = source.relative_to(LEAN_ROOT).with_suffix(".olean")
        pairs.append((source, LEAN_ROOT / ".lake/build/lib/lean" / relative))
    errors: list[str] = []
    for source, olean in pairs:
        if not olean.exists():
            errors.append(f"missing {olean.relative_to(ROOT).as_posix()}")
        elif olean.stat().st_mtime_ns < source.stat().st_mtime_ns:
            errors.append(
                f"stale {olean.relative_to(ROOT).as_posix()} for "
                f"{source.relative_to(ROOT).as_posix()}"
            )
    return errors


def first_error(output: str) -> str | None:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    for line in lines:
        if re.search(r"\berror(?:\[|:|\()", line, flags=re.IGNORECASE) or "failed" in line.lower():
            return line[:500]
    return lines[0][:500] if lines else None


def kernel_class(exit_code: int | None, output: str) -> str:
    if exit_code is None:
        return "not_run"
    if exit_code == 0:
        return "pass"
    if "object file" in output and "does not exist" in output:
        return "infrastructure_failure"
    return "kernel_reject"


def forbidden_output_hits(path: Path) -> list[str]:
    if not path.exists():
        return []
    return [
        f"{line_number}:{line.strip()}"
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        )
        if FORBIDDEN_OUTPUT.search(line)
    ]


def snapshot_is_stable(
    compiler_before: str | None,
    compiler_after: str | None,
    examples_before: str,
    examples_after: str,
    lean_before: str,
    lean_after: str,
    rust_before_build: str,
    rust_after_build: str,
    rust_before_matrix: str,
    rust_after_matrix: str,
    olean_errors_after: list[str],
) -> bool:
    return (
        compiler_before is not None
        and compiler_before == compiler_after
        and examples_before == examples_after
        and lean_before == lean_after
        and rust_before_build
        == rust_after_build
        == rust_before_matrix
        == rust_after_matrix
        and not olean_errors_after
    )


def run(command: list[str], cwd: Path) -> tuple[int, str]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.returncode, completed.stdout


def registered_sources() -> list[Path]:
    config = (EXAMPLES / "litex.config").read_text(encoding="utf-8")
    return [
        source
        for source in sorted(EXAMPLES.glob("*.lit"))
        if f'"./{source.name}"' in config
    ]


def clear_generated_output(path: Path) -> None:
    if path.exists():
        if not path.is_file():
            raise ValueError(f"generated output target is not a file: {path}")
        path.unlink()


def check_example(source: Path, output_dir: Path) -> dict[str, object]:
    checked = source.with_suffix(".lean")
    generated = output_dir / checked.name
    clear_generated_output(generated)
    compiler_exit, compiler_output = run(
        [str(COMPILER), "compile", str(source), str(generated)], ROOT
    )
    if compiler_exit == 0:
        generated_kernel_exit, generated_kernel_output = run(
            ["lake", "env", "lean", str(generated)], LEAN_ROOT
        )
    else:
        generated_kernel_exit = None
        generated_kernel_output = ""
    checked_kernel_exit, checked_kernel_output = run(
        ["lake", "env", "lean", str(checked)], LEAN_ROOT
    )
    generated_hash = sha256(generated)
    checked_hash = sha256(checked)
    return {
        "example": source.name,
        "source_sha256": sha256(source),
        "checked_in_path": checked.relative_to(ROOT).as_posix(),
        "checked_in_sha256": checked_hash,
        "compiler_exit": compiler_exit,
        "generated_path": generated.relative_to(ROOT).as_posix(),
        "generated_sha256": generated_hash,
        "generated_kernel_exit": generated_kernel_exit,
        "generated_kernel_class": kernel_class(
            generated_kernel_exit, generated_kernel_output
        ),
        "generated_kernel_first_error": first_error(generated_kernel_output),
        "checked_in_kernel_exit": checked_kernel_exit,
        "checked_in_kernel_class": kernel_class(
            checked_kernel_exit, checked_kernel_output
        ),
        "checked_in_kernel_first_error": first_error(checked_kernel_output),
        "matches_checked_in": bool(generated_hash and generated_hash == checked_hash),
        "generated_forbidden_hits": forbidden_output_hits(generated),
        "checked_in_forbidden_hits": forbidden_output_hits(checked),
        "compiler_first_error": first_error(compiler_output),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()

    output_dir = args.output_dir.resolve()
    report_path = args.report.resolve()
    tmp_root = TMP_ROOT.resolve()
    if output_dir != tmp_root and tmp_root not in output_dir.parents:
        parser.error("--output-dir must be inside the workspace tmp/ directory")
    if args.jobs < 1 or args.jobs > 8:
        parser.error("--jobs must be between 1 and 8")
    if report_path != DEFAULT_REPORT.resolve():
        parser.error(f"--report must be {DEFAULT_REPORT.relative_to(ROOT)}")
    olean_errors_before = lean_olean_precondition_errors()
    if olean_errors_before:
        parser.error(
            "Lean dependencies are not freshly built; run `cd lean && lake build`: "
            + olean_errors_before[0]
        )
    rust_fingerprint_before_build = rust_source_fingerprint()
    compiler_build_exit, compiler_build_output = run(
        ["cargo", "build", "--release", "--bin", "stmt_result_to_lean_compiler"],
        ROOT,
    )
    rust_fingerprint_after_build = rust_source_fingerprint()
    if compiler_build_exit != 0:
        print(
            "release compiler build failed: "
            + str(first_error(compiler_build_output)),
        )
        return 1
    if rust_fingerprint_before_build != rust_fingerprint_after_build:
        print("Rust sources changed while binding the release compiler")
        return 1
    if not COMPILER.exists():
        print(f"release compiler build did not create {COMPILER}")
        return 1
    output_dir.mkdir(parents=True, exist_ok=True)

    sources = registered_sources()
    compiler_fingerprint_before = sha256(COMPILER)
    example_fingerprint_before = example_input_fingerprint(sources)
    dependency_fingerprint_before = lean_dependency_fingerprint()
    rust_fingerprint_before_matrix = rust_source_fingerprint()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        rows = list(executor.map(lambda source: check_example(source, output_dir), sources))
    dependency_fingerprint_after = lean_dependency_fingerprint()
    compiler_fingerprint_after = sha256(COMPILER)
    example_fingerprint_after = example_input_fingerprint(sources)
    rust_fingerprint_after_matrix = rust_source_fingerprint()
    olean_errors_after = lean_olean_precondition_errors()
    rows.sort(key=lambda row: str(row["example"]))
    totals = {
        "registered": len(rows),
        "compiler_pass": sum(row["compiler_exit"] == 0 for row in rows),
        "matches_checked_in": sum(row["matches_checked_in"] for row in rows),
    }
    for prefix in ("generated_kernel", "checked_in_kernel"):
        for classification in (
            "pass",
            "kernel_reject",
            "infrastructure_failure",
            "not_run",
        ):
            totals[f"{prefix}_{classification}"] = sum(
                row[f"{prefix}_class"] == classification for row in rows
            )
    totals["generated_forbidden_rows"] = sum(
        bool(row["generated_forbidden_hits"]) for row in rows
    )
    totals["checked_in_forbidden_rows"] = sum(
        bool(row["checked_in_forbidden_hits"]) for row in rows
    )
    stable = snapshot_is_stable(
        compiler_fingerprint_before,
        compiler_fingerprint_after,
        example_fingerprint_before,
        example_fingerprint_after,
        dependency_fingerprint_before,
        dependency_fingerprint_after,
        rust_fingerprint_before_build,
        rust_fingerprint_after_build,
        rust_fingerprint_before_matrix,
        rust_fingerprint_after_matrix,
        olean_errors_after,
    )
    report = {
        "schema_version": 3,
        "recorded_at": datetime.now(ZoneInfo("Asia/Shanghai")).strftime(
            "%Y-%m-%d %H:%M:%S %Z"
        ),
        "command": (
            "python3 lean/coverage/kernel_check_examples.py "
            f"--output-dir {output_dir.relative_to(ROOT).as_posix()} --jobs {args.jobs}"
        ),
        "compiler_path": COMPILER.relative_to(ROOT).as_posix(),
        "compiler_build_command": "cargo build --release --bin stmt_result_to_lean_compiler",
        "compiler_build_exit": compiler_build_exit,
        "rust_source_fingerprint_before_build": rust_fingerprint_before_build,
        "rust_source_fingerprint_after_build": rust_fingerprint_after_build,
        "rust_source_fingerprint_before_matrix": rust_fingerprint_before_matrix,
        "rust_source_fingerprint_after_matrix": rust_fingerprint_after_matrix,
        "rust_source_stable_during_build_and_matrix": (
            rust_fingerprint_before_build
            == rust_fingerprint_after_build
            == rust_fingerprint_before_matrix
            == rust_fingerprint_after_matrix
        ),
        "compiler_sha256": compiler_fingerprint_after,
        "compiler_fingerprint_before": compiler_fingerprint_before,
        "compiler_fingerprint_after": compiler_fingerprint_after,
        "compiler_stable_during_run": (
            compiler_fingerprint_before == compiler_fingerprint_after
        ),
        "example_input_fingerprint_before": example_fingerprint_before,
        "example_input_fingerprint_after": example_fingerprint_after,
        "example_inputs_stable_during_run": (
            example_fingerprint_before == example_fingerprint_after
        ),
        "lean_dependency_fingerprint_before": dependency_fingerprint_before,
        "lean_dependency_fingerprint_after": dependency_fingerprint_after,
        "lean_dependency_stable_during_run": (
            dependency_fingerprint_before == dependency_fingerprint_after
        ),
        "core_olean_present_after_run": (
            LEAN_ROOT / ".lake/build/lib/lean/Litex/Core.olean"
        ).exists(),
        "olean_precondition_errors_before": olean_errors_before,
        "olean_precondition_errors_after": olean_errors_after,
        "snapshot_valid": stable,
        "totals": totals,
        "rows": rows,
    }
    report_path.write_text(
        json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(totals, sort_keys=True))
    if dependency_fingerprint_before != dependency_fingerprint_after:
        print("Lean dependency sources changed during the matrix run")
    if compiler_fingerprint_before != compiler_fingerprint_after:
        print("release compiler binary changed during the matrix run")
    if example_fingerprint_before != example_fingerprint_after:
        print("registered example inputs changed during the matrix run")
    if not (
        rust_fingerprint_before_build
        == rust_fingerprint_after_build
        == rust_fingerprint_before_matrix
        == rust_fingerprint_after_matrix
    ):
        print("Rust sources changed during compiler binding or the matrix run")
    if olean_errors_after:
        print("Lean object dependencies became missing or stale during the matrix run")
    failures = [
        row
        for row in rows
        if row["compiler_exit"] != 0
        or row["generated_kernel_class"] != "pass"
        or row["checked_in_kernel_class"] != "pass"
        or row["generated_forbidden_hits"]
        or row["checked_in_forbidden_hits"]
    ]
    for row in failures:
        print(
            f"{row['example']}: compiler={row['compiler_exit']} "
            f"generated_kernel={row['generated_kernel_class']} "
            f"checked_kernel={row['checked_in_kernel_class']} "
            f"compiler_error={row['compiler_first_error']} "
            f"generated_error={row['generated_kernel_first_error']} "
            f"checked_error={row['checked_in_kernel_first_error']}"
        )
    return 1 if failures or not stable else 0


if __name__ == "__main__":
    raise SystemExit(main())
