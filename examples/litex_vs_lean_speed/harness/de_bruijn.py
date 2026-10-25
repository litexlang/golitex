#!/usr/bin/env python3
"""Report retrospective character-based de Bruijn factors; never run a prover.

    python3 examples/litex_vs_lean_speed/harness/de_bruijn.py --write
    python3 examples/litex_vs_lean_speed/harness/de_bruijn.py --check

The first command writes the size record and refreshes the three existing
generated tables from their saved timing summaries. Neither command changes
proof sources, raw samples, timing summaries, or environment records.
"""

import argparse
import hashlib
import json
from pathlib import Path
import statistics

BENCH = Path(__file__).resolve().parents[1]
BASELINES = BENCH / "cases/informal-baselines.json"
BATCHES = ("new-round", "multi-step", "statement-forms")
TABLE_NOTE = (
    "**表达长度**：德布鲁因因子 DF* = 该语言有效字符数 ÷ 同题普通数学有效字符数，越小越简短。"
    "**运行速度**：耗时单位为毫秒；Litex 加速比 = Lean 耗时 ÷ Litex 耗时，越大表示 Litex 越快。"
    "这是共享英文数学文本的回溯示例，非预先选定原文的翻译实验；"
    "— 表示缺少基线或源码与计时用例定义不一致。"
    "[原文、口径与限制](../README.md#de-bruijn-factor)。"
)


def normalized_text(text, formal=False):
    """Use the existing types-and-objects guide's full-line exclusion rule."""
    lines = text.splitlines()
    if formal:
        lines = [line for line in lines if not line.strip().startswith(
            ("#", "--", "import ", "set_option "))]
    return "".join("".join(lines).split())


def baselines():
    data = json.loads(BASELINES.read_text(encoding="utf-8"))
    for key, entry in data["entries"].items():
        if not normalized_text(entry["text"]) or not entry["scope"]:
            raise ValueError(f"empty informal baseline or scope: {key}")
    return data


def source_record(path, denominator):
    body = path.read_text(encoding="utf-8")
    count = len(normalized_text(body, formal=True))
    if count == 0 or denominator <= 0:
        raise ValueError(f"empty source or denominator: {path}")
    return {
        "path": str(path.relative_to(BENCH)),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "characters": count,
        "de_bruijn_factor": count / denominator,
    }


def source_matches(path, expected):
    return normalized_text(path.read_text(encoding="utf-8"), True) == normalized_text(expected, True)


def factor_cells(batch, case, litex_path, lean_path, method):
    entry = baselines()["entries"].get(f'{batch}/{case["id"]}')
    if entry is None:
        return "—", "—"
    expected_lean = f'example : {case["lean"]} := {case["methods"][method]}'
    if not source_matches(litex_path, case["litex"]) or not source_matches(lean_path, expected_lean):
        return "—", "—"
    denominator = len(normalized_text(entry["text"]))
    litex = source_record(litex_path, denominator)
    lean = source_record(lean_path, denominator)
    return f'{litex["de_bruijn_factor"]:.2f}', f'{lean["de_bruijn_factor"]:.2f}'


def build_record():
    data = baselines()
    entries = {}
    excluded = {}
    inputs = [BASELINES, Path(__file__).resolve(), Path(__file__).with_name("bench.py")]
    for batch in BATCHES:
        case_file = BENCH / f"cases/{batch}.json"
        summary_file = BENCH / f"results/{batch}-summary.json"
        raw_file = BENCH / f"results/{batch}-raw.json"
        inputs.extend((case_file, summary_file, raw_file))
        cases = json.loads(case_file.read_text(encoding="utf-8"))
        summary = json.loads(summary_file.read_text(encoding="utf-8"))
        groups = {}
        for sample in json.loads(raw_file.read_text(encoding="utf-8")):
            if sample["rep"] != "first":
                key = f'{sample["system"]}/{sample["case"]}'
                groups.setdefault(key, []).append(sample["ms"])
        for key, values in groups.items():
            if (summary[key]["median_ms"] != statistics.median(values)
                    or summary[key]["n"] != len(values)):
                raise ValueError(f"timing summary/raw mismatch: {batch}/{key}")
        if groups.keys() != summary.keys():
            raise ValueError(f"timing summary/raw group mismatch: {batch}")
        for case in cases:
            key = f'{batch}/{case["id"]}'
            if key not in data["entries"]:
                continue
            entry = dict(data["entries"][key])
            denominator = len(normalized_text(entry["text"]))
            entry["informal_characters"] = denominator
            litex_path = BENCH / f'sources/{batch}/{case["id"]}.lit'
            paths = {"litex": (litex_path, case["litex"])}
            paths.update({method: (
                BENCH / f'sources/{batch}/{case["id"]}__{method}.lean',
                f'example : {case["lean"]} := {proof}',
            ) for method, proof in case["methods"].items()})
            drift = [str(path.relative_to(BENCH)) for path, expected in paths.values()
                     if not source_matches(path, expected)]
            if drift:
                excluded[key] = {
                    "reason": "Published source differs from saved timing-case definition; no factors attached to historical times.",
                    "drifted_sources": {str(path.relative_to(BENCH)): hashlib.sha256(path.read_bytes()).hexdigest()
                                        for path, _ in paths.values() if str(path.relative_to(BENCH)) in drift},
                }
                continue
            entry["litex"] = source_record(litex_path, denominator)
            entry["lean"] = {}
            for method, proof in case["methods"].items():
                lean_path = BENCH / f'sources/{batch}/{case["id"]}__{method}.lean'
                entry["lean"][method] = source_record(lean_path, denominator)
            entry["timing_summary"] = str(summary_file.relative_to(BENCH))
            entries[key] = entry

    key = "declarations/guarded_function"
    entry = dict(data["entries"][key])
    denominator = len(normalized_text(entry["text"]))
    entry["informal_characters"] = denominator
    entry["litex"] = source_record(BENCH / f"sources/{key}.lit", denominator)
    entry["lean"] = {"paired": source_record(BENCH / f"sources/{key}.lean", denominator)}
    entry["timing_summary"] = None
    entry["timing_note"] = "The types guide has only a historical rounded timing aggregate for this pair; no new timing data or raw-sample validation is supplied here."
    entries[key] = entry
    if entries.keys() | excluded.keys() != data["entries"].keys():
        raise ValueError("baseline keys do not match the supported source corpus")
    return {
        "metric": "retrospective normalized-character de Bruijn factor (DF*)",
        "formula": "formal_characters / informal_characters; lower is shorter",
        "provenance": data["provenance"],
        "language": data["language"],
        "counting_rule": "Count Unicode code points after removing all whitespace. For formal sources also exclude full lines starting (after stripping) with #, --, import followed by a space, or set_option followed by a space. Include declarations, names, statements and proofs; exclude library/builtin implementations on both sides. This is not a byte-count or gzip-compressed factor.",
        "source_boundary": "Counts use the published standalone sources and check their correspondence to the saved case definitions. The older timing cohorts have no time-of-run source hashes; this audit does not retroactively establish such hashes.",
        "inputs_sha256": {str(p.relative_to(BENCH)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        "entries": entries,
        "excluded": excluded,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    record = build_record()
    outputs = {BENCH / "results/de-bruijn-factors.json": json.dumps(record, ensure_ascii=False, indent=2) + "\n"}
    import bench
    for batch in BATCHES:
        bench.SOURCES = BENCH / f"sources/{batch}"
        cases = json.loads((BENCH / f"cases/{batch}.json").read_text(encoding="utf-8"))
        summary = json.loads((BENCH / f"results/{batch}-summary.json").read_text(encoding="utf-8"))
        outputs[BENCH / f"results/{batch}.md"] = bench.markdown(cases, summary) + "\n"
    if args.write:
        for path, text in outputs.items():
            path.write_text(text, encoding="utf-8")
    elif args.check:
        stale = [str(p.relative_to(BENCH)) for p, text in outputs.items()
                 if not p.exists() or p.read_text(encoding="utf-8") != text]
        if stale:
            raise SystemExit("stale reports: " + ", ".join(stale))
    print(f"Audited {len(record['entries'])} source-matched pairs; "
          f"{len(record['excluded'])} drifted pairs omitted; "
          f"{len(outputs)} reports {'written' if args.write else 'checked' if args.check else 'computed'}; no prover or timer invoked.")


if __name__ == "__main__":
    main()
