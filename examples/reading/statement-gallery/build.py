#!/usr/bin/env python3
"""Build the review-only statement gallery from current checked repository examples."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SUITE = ROOT / "examples/test_statements"


def source_for(design, entries):
    entry = entries[design["leaf"]]
    if "source" in design:
        path = ROOT / design["source"]
        start, end = design["lines"]
        source = "\n".join(path.read_text().splitlines()[start - 1:end]) + "\n"
        return source, str(path.relative_to(ROOT)), True
    path = SUITE / entry["file"]
    source = path.read_text()
    markers = list(re.finditer(r"^# case:.*$", source, re.M))
    index = design.get("case", 0)
    if markers:
        start = markers[index].end()
        end = markers[index + 1].start() if index + 1 < len(markers) else len(source)
        source = source[start:end].strip() + "\n"
    strict = entry["cases"][index]["strict"] if entry.get("cases") else entry["file_strict"]
    return source, str(path.relative_to(ROOT)), strict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/litex")
    args = parser.parse_args()
    output, binary = args.output.resolve(), args.binary.resolve()
    if output == HERE or HERE in output.parents:
        parser.error("Keep generated sites outside the maintained gallery source directory")
    manifest = json.loads((SUITE / "manifest.json").read_text())
    spec = importlib.util.spec_from_file_location("statement_inventory", SUITE / "run.py")
    inventory = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inventory)
    inventory.audit_inventory(manifest)
    entries = {entry["leaf"]: entry for entry in manifest["statements"]}
    designs = json.loads((HERE / "designs.json").read_text())
    primary = [design["leaf"] for design in designs if not design.get("fact_form")]
    if len(primary) != len(set(primary)) or set(primary) != set(entries):
        raise ValueError("Primary designs must cover every current AST statement leaf exactly once")
    if len({design["id"] for design in designs}) != len(designs):
        raise ValueError("Duplicate design IDs")
    output.mkdir(parents=True, exist_ok=True)
    (output / "evidence").mkdir(exist_ok=True)
    (output / "examples").mkdir(exist_ok=True)

    def check(design):
        source, origin, strict = source_for(design, entries)
        command = [str(binary), "-reading", "-json", "-lang", "zh"]
        if strict:
            command.append("-strict")
        command.extend(["-e", source])
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=60)
        raw_path = output / "evidence" / (design["id"] + ".json")
        raw_path.write_text(result.stdout)
        bundle = json.loads(result.stdout)
        if result.returncode or bundle.get("run_result") != "success":
            raise ValueError(f"Example failed: {design['id']}: {bundle.get('diagnostics')} {result.stderr}")
        source_bytes = source.encode()
        candidates = []
        for stmt in bundle["statements"]:
            if stmt.get("statement_kind", "").split(".")[-1] != design["leaf"]:
                continue
            fragment = source_bytes[stmt["start_byte"]:stmt["end_byte"]].decode()
            if design.get("focus") and not fragment.lstrip().startswith(design["focus"]):
                continue
            if stmt["status"] == "accepted":
                candidates.append(stmt)
        if not candidates:
            raise ValueError(f"No actual accepted target of kind {design['leaf']} for {design['id']}")
        target = candidates[0]
        first = source_bytes[:target["start_byte"]].count(b"\n") + 1
        last = source_bytes[:target["end_byte"]].rstrip(b"\n").count(b"\n") + 1
        fact_map = {fact["id"]: fact for fact in bundle["facts"]}
        if design.get("expected_published"):
            actual = {fact_map[key]["text"] for key in target.get("produced_fact_ids", []) if key in fact_map}
            if design["expected_published"] not in actual:
                raise ValueError(f"Displayed computation is not an actual published result: {design['id']}")
        inferred = []
        seen = set()
        for stmt in bundle["statements"]:
            published = set(stmt.get("produced_fact_ids", []))
            for fact_id in stmt.get("inferred_fact_ids", []):
                if fact_id in published and fact_id in fact_map and fact_id not in seen:
                    seen.add(fact_id)
                    inferred.append({"id": fact_id, "text": fact_map[fact_id]["text"], "line": stmt["line"]})
        trust = bundle.get("trust_summary", {})
        record = dict(design, code=source, origin=origin, strict=strict,
                      focus_lines=[first, last], inferred=inferred,
                      statement_kind=target["statement_kind"],
                      trust_count=len(trust.get("user_assumptions", [])) + len(trust.get("axioms", [])),
                      source_sha256=hashlib.sha256(source_bytes).hexdigest())
        (output / "examples" / (design["id"] + ".lit")).write_text(source)
        print("CHECKED", design["id"], flush=True)
        return record

    with ThreadPoolExecutor(max_workers=4) as pool:
        records = list(pool.map(check, designs))
    for name in ["index.html", "gallery.css", "gallery.js"]:
        shutil.copyfile(HERE / name, output / name)
    web = ROOT / "src/reading/web"
    shutil.copyfile(web / "reader.css", output / "reader.css")
    for name in ["katex.min.js", "katex.min.css", "LICENSE"]:
        shutil.copyfile(web / "vendor/katex" / name, output / ("katex.LICENSE" if name == "LICENSE" else name))
    payload = {"leaf_count": len(entries), "designs": records}
    (output / "catalogue.js").write_text("window.LitexStatementGallery = " + json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c") + ";\n")
    html = (output / "index.html").read_text()
    for name in ["katex.min.js", "katex.min.css", "reader.css", "gallery.css", "gallery.js", "catalogue.js"]:
        digest = hashlib.sha256((output / name).read_bytes()).hexdigest()[:12]
        html = html.replace('"' + name + '"', '"' + name + '?v=' + digest + '"')
    (output / "index.html").write_text(html)
    acceptance = {"statement_leaves": len(entries), "examples": len(records), "all_examples_passed": True,
                  "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
                  "designs_sha256": hashlib.sha256((HERE / "designs.json").read_bytes()).hexdigest(),
                  "examples_checked": [{"id": r["id"], "leaf": r["leaf"], "statement_kind": r["statement_kind"],
                                        "source_sha256": r["source_sha256"], "strict": r["strict"]} for r in records]}
    (output / "acceptance.json").write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + "\n")
    print(f"Built {len(records)} examples covering all {len(entries)} statement leaves: {output}")


if __name__ == "__main__":
    main()
