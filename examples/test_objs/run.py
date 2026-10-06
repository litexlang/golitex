#!/usr/bin/env python3
"""Run the Obj corpus and fail closed on crashes, bad JSON or uncovered AST leaves."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--object", action="append", help="Select a manifest object name; repeat to select several")
    parser.add_argument("--baseline", action="store_true", help="Check the recorded behavior of every known gap; this does not certify its intended semantics")
    parser.add_argument("--audit-only", action="store_true", help="Audit AST and fixture inventory without launching Litex")
    parser.add_argument("--report", type=Path, help="Save structured observations to this JSON path")
    parser.add_argument("--timeout", type=float, default=30, help="Maximum seconds per Litex process (default: 30)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    suite = Path(__file__).resolve().parent
    root = suite.parents[1]
    manifest = json.loads((suite / "coverage.json").read_text())
    problems = audit(suite, root, manifest)
    if problems:
        for problem in problems:
            print("AUDIT FAILED: " + problem, file=sys.stderr)
        return 1
    objects = manifest["objects"]
    if args.object:
        unknown = set(args.object) - {obj["name"] for obj in objects}
        if unknown:
            parser.error("unknown object: " + ", ".join(sorted(unknown)))
        objects = [obj for obj in objects if obj["name"] in args.object]
    leaf_count = sum(len(obj["ast_paths"]) for obj in manifest["objects"])
    if args.audit_only:
        active_count = sum(not obj.get("retired", False) for obj in manifest["objects"])
        print(f"AST inventory passed: {leaf_count} Obj leaves, {active_count} positive files, "
              f"{len(manifest['objects']) - active_count} retired interface families with rejection fixtures.")
        return 0

    build_source = source_digest(root)
    build = subprocess.run(['cargo', 'build', '--release'], cwd=root, capture_output=True, text=True)
    if build.returncode != 0:
        print('Current-source release build failed; no Litex fixture was executed.', file=sys.stderr)
        diagnostics = build.stdout + build.stderr
        errors = re.findall(r'^error.*(?:\n(?!error).*){0,12}', diagnostics, re.MULTILINE)
        print('\n\n'.join(errors[:3]) or diagnostics[-2000:], file=sys.stderr)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps({'schema_version': 1, 'ok': False,
                'built_from_current_source': False, 'observations': [], 'phase': 'build',
                'exit_code': build.returncode, 'diagnostic': '\n\n'.join(errors[:3]) or diagnostics[-2000:]}, indent=2) + '\n')
        return 1
    if build_source != source_digest(root):
        print('Source changed during the build; rerun after the update. No Litex fixture was executed.', file=sys.stderr)
        return 1
    binary = root / "target/release/litex"
    if not binary.is_file():
        print("Build the current source first: cargo build --release", file=sys.stderr)
        return 1
    report = {"schema_version": 1, "mode": "baseline" if args.baseline else "intended",
        "built_from_current_source": True,
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "source_sha256": build_source,
        "ast_sha256": hashlib.sha256((root / manifest["ast_source"]).read_bytes()).hexdigest(),
        "objects": len(objects), "positive_assertions": sum(len(obj["positive_cases"]) for obj in objects),
        "observations": [], "failures": [], "known_gaps": []}
    for obj in objects:
        fixtures = [] if obj.get("retired", False) else [("positive", obj["positive_file"], "accept", None)]
        gaps = {gap["file"]: gap for gap in obj["gaps"]}
        for case in obj["negative_cases"]:
            fixtures.append(("negative", case["file"], "reject", gaps.get(case["file"])))
        for gap in obj["gaps"]:
            if gap["intended"] == "accept":
                fixtures.append(("gap", gap["file"], "accept", gap))
        for kind, file, intended, gap in fixtures:
            result = evaluate(binary, root, suite / file, args.timeout)
            result.update({"object": obj["name"], "file": file, "kind": kind, "intended": intended})
            observed = result["observed"]
            expected = gap["baseline"]["observed"] if args.baseline and gap else intended
            matches = observed == expected
            if kind == "positive" and observed == "accept":
                # Each labeled independent sketch must actually have executed.
                matches = matches and result["statements"] >= len(obj["positive_cases"])
            if args.baseline and gap and observed == "reject":
                matches = matches and result["phase"] == gap["baseline"]["phase"]
            if gap:
                report["known_gaps"].append({"object": obj["name"], "file": file, "intended": intended,
                    "observed": observed, "issue": gap["issue"]})
            if not matches:
                report["failures"].append({"file": file, "expected": expected, "observed": observed,
                    "phase": result["phase"], "diagnostic": result["diagnostic"]})
            report["observations"].append(result)

    report["binary_stable"] = report['binary_sha256'] == hashlib.sha256(binary.read_bytes()).hexdigest()
    report["source_stable"] = report['source_sha256'] == source_digest(root)
    if not report['binary_stable'] or not report['source_stable']:
        report['failures'].append({'file': '<workspace>', 'expected': 'stable source and binary',
            'observed': 'changed during gate', 'phase': 'infrastructure',
            'diagnostic': 'Build the current source and rerun; this gate spanned different workspace states.'})
    report["ok"] = not report["failures"]
    counts = {kind: sum(item["kind"] == kind for item in report["observations"]) for kind in ("positive", "negative", "gap")}
    print(f"Checked {report['objects']} objects: {report['positive_assertions']} positive cases in {counts['positive']} files; "
          f"{counts['negative']} rejection fixtures; {counts['gap']} positive-gap reproductions.")
    print(f"Known semantic gaps: {len(report['known_gaps'])}; gate failures: {len(report['failures'])}.")
    for failure in report["failures"][:12]:
        print(f"FAIL {failure['file']}: expected {failure['expected']}, observed {failure['observed']} ({failure['phase']})")
    if len(report["failures"]) > 12:
        print("Remaining failures are listed in todo.md and the structured report.")
    if args.baseline and report["ok"]:
        print("Recorded baseline reproduced. Known gaps remain; this is not a full semantic pass.")
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["ok"] else 1


def ast_enums(source):
    source = re.sub(r"//[^\n]*", "", source)
    enums = {}
    for match in re.finditer(r"pub enum (\w+)\s*\{", source):
        start = match.end()
        depth = 1
        end = start
        while depth and end < len(source):
            depth += (source[end] == "{") - (source[end] == "}")
            end += 1
        body = source[start:end - 1]
        variants = []
        entries = []
        entry = ""
        nesting = 0
        for char in body + ",":
            nesting += char in "({["
            nesting -= char in ")}]"
            if char == "," and nesting == 0:
                if entry.strip():
                    entries.append(entry.strip())
                entry = ""
            else:
                entry += char
        for entry in entries:
            variant = re.fullmatch(r"(\w+)(?:\s*\((.*)\)|\s*\{.*\})?", entry, re.DOTALL)
            if not variant:
                raise ValueError("Unsupported enum entry in " + match[1] + ": " + entry)
            variants.append((variant[1], variant[2].strip() if variant[2] else None))
        if not variants:
            raise ValueError("No variants parsed for " + match[1])
        enums[match[1]] = variants
    return enums


def source_digest(root):
    digest = hashlib.sha256()
    paths = sorted((root / 'src').rglob('*.rs')) + [root / 'Cargo.toml', root / 'Cargo.lock']
    for path in paths:
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b'\0')
        digest.update(path.read_bytes())
    return digest.hexdigest()


def audit(suite, root, manifest):
    enums = ast_enums((root / manifest["ast_source"]).read_text())
    leaves = set()

    def visit(enum_name, prefix):
        for variant, payload in enums[enum_name]:
            path = prefix + "::" + variant
            if payload in enums:
                visit(payload, path)
            else:
                leaves.add(path)

    visit("Obj", "Obj")
    covered = [path for obj in manifest["objects"] for path in obj["ast_paths"]]
    errors = []
    for path in sorted(leaves - set(covered)):
        errors.append("uncovered AST leaf " + path)
    for path in sorted(set(covered) - leaves):
        errors.append("stale AST path " + path)
    if len(covered) != len(set(covered)):
        errors.append("duplicate AST leaf mapping")
    helpers = {path for obj in manifest["objects"] for path in obj.get("helper_paths", [])}
    for name in ("FnObjHead", "FnSetSpace"):
        for variant, _ in enums[name]:
            if name + "::" + variant not in helpers:
                errors.append("uncovered helper variant " + name + "::" + variant)
    expected_files = set(manifest.get("auxiliary_files", []))
    object_names = [obj["name"] for obj in manifest["objects"]]
    if len(object_names) != len(set(object_names)):
        errors.append("duplicate object name")
    targets = [obj['positive_file'] for obj in manifest['objects'] if not obj.get("retired", False)]
    if len(targets) != len(set(targets)):
        errors.append("several objects share the same dedicated file")
    for obj in manifest["objects"]:
        retired = obj.get("retired", False)
        if retired and (obj.get("positive_file") is not None or obj["positive_cases"] or obj["gaps"]):
            errors.append("retired interface still has positive obligations: " + obj["name"])
        if retired and not obj.get("retired_reason"):
            errors.append("retired interface lacks an explicit reason: " + obj["name"])
        if not retired and not obj["positive_cases"]:
            errors.append("no accepted case for " + obj["name"])
        if not obj["negative_cases"]:
            errors.append("no executable negative for " + obj["name"])
        for key in ("negative_cases", "gaps"):
            for record in obj[key]:
                expected_files.add(record["file"])
                if key == "gaps" and record["intended"] == record["baseline"]["observed"]:
                    errors.append("resolved/stale gap " + record["file"])
        if not retired:
            expected_files.add(obj["positive_file"])
            target = suite / obj["positive_file"]
            if target.is_file():
                ids = re.findall(r"^# (P\d+):", target.read_text(), re.MULTILINE)
                if ids != obj["positive_cases"]:
                    errors.append("positive case labels differ from manifest: " + obj["positive_file"])
    for file in sorted(expected_files):
        path = suite / file
        if not path.is_file():
            errors.append("missing fixture " + file)
        elif path.suffix == ".lit":
            code = re.sub(r"#.*", "", path.read_text()).strip()
            if not code:
                errors.append("empty fixture " + file)
            if re.search(r"\btrust\b", code):
                errors.append("trust in fixture " + file)
    actual_files = {str(path.relative_to(suite)) for path in suite.rglob("*.lit")}
    for file in sorted(actual_files - expected_files):
        errors.append("untracked fixture " + file)
    return errors


def evaluate(binary, root, path, timeout):
    command = [str(binary), "-f", str(path.relative_to(root))]
    try:
        process = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"observed": "infrastructure_failure", "exit_code": None, "phase": "timeout", "diagnostic": "process timed out", "statements": 0}
    try:
        envelope = json.loads(process.stdout)
    except json.JSONDecodeError:
        return {"observed": "infrastructure_failure", "exit_code": process.returncode, "phase": "invalid_json", "diagnostic": (process.stderr + process.stdout)[-2000:], "statements": 0}
    if not isinstance(envelope, dict) or envelope.get("kind") != "run" or type(envelope.get("success")) is not bool:
        return {"observed": "infrastructure_failure", "exit_code": process.returncode, "phase": "invalid_envelope", "diagnostic": repr(envelope)[-2000:], "statements": 0}
    statements = envelope.get("statement_results", [])
    failed = [result for result in statements if result.get("success") is False]
    error = envelope.get("session_error")
    observed = "infrastructure_failure"
    phase = "protocol"
    diagnostic = process.stderr
    if envelope["success"] is True and process.returncode == 0 and not failed and error is None:
        observed, phase = "accept", "success"
    elif envelope["success"] is False and process.returncode == 1:
        parse_error = isinstance(error, str) and error.startswith(("parse_error:", "Runtime(ParseError("))
        if failed and (error is None or parse_error):
            observed = "reject"
            phase = failed[0].get("why_failed", {}).get("phase", "verification")
            diagnostic = json.dumps(failed[0], ensure_ascii=False)
            if error:
                diagnostic += "; subsequent error: " + error
        elif parse_error:
            observed, phase, diagnostic = "reject", "parse", error
    return {"observed": observed, "exit_code": process.returncode, "phase": phase,
        "diagnostic": diagnostic, "statements": len(statements)}


if __name__ == "__main__":
    sys.exit(main())
