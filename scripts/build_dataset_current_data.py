#!/usr/bin/env python3
"""Build public current_data.json files for Litex dataset workspaces."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import shutil
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
TEMPLATE = SCRIPTS / "dataset_review_dashboard.html"

BLOCKER_LABELS = (
    "blocked_by_language",
    "blocked_by_stdlib",
    "blocked_by_infer_rule",
    "blocked_by_kernel",
    "blocked_by_syntax",
    "blocked_by_diagnostics",
    "blocked_by_formulation",
)


DATASETS = {
    "MATH-500-litex": {
        "title": "MATH-500 Litex",
        "source": "MATH-500",
        "path": SCRIPTS / "MATH-500-litex",
        "kind": "math500",
        "repository": "MATH-500-litex",
    },
    "litex-minif2f": {
        "title": "MiniF2F Litex",
        "source": "MiniF2F",
        "path": SCRIPTS / "litex-minif2f",
        "kind": "minif2f",
        "repository": "litex-minif2f",
    },
    "math23k-litex": {
        "title": "Math23K Litex",
        "source": "Math23K",
        "path": SCRIPTS / "math23k-litex",
        "kind": "simple_jsonl",
        "repository": "math23k-litex",
        "files": [("all", "litex_dataset/math23k.jsonl", "translated")],
        "topic": "Chinese arithmetic word problem",
    },
    "gsm8k-litex": {
        "title": "GSM8K Litex",
        "source": "GSM8K",
        "path": SCRIPTS / "gsm8k-litex",
        "kind": "simple_jsonl",
        "repository": "gsm8k-litex",
        "files": [
            ("train", "litex_dataset/train.jsonl", "translated"),
            ("test", "litex_dataset/test.jsonl", "translated"),
        ],
        "topic": "arithmetic word problem",
    },
    "MetaMathQA-litex": {
        "title": "MetaMathQA Litex",
        "source": "MetaMathQA",
        "path": SCRIPTS / "MetaMathQA-litex",
        "kind": "simple_jsonl",
        "repository": "litex-metamathqa",
        "files": [
            ("aligned", "litex_dataset/MetaMathQA.jsonl", "translated"),
            ("unfinished", "unfinished_dataset/MetaMathQA.not_ok.jsonl", "blocked"),
        ],
        "topic": "generated arithmetic word problem",
    },
    "high_school_book": {
        "title": "High School Math Litex",
        "source": "High School Book",
        "path": SCRIPTS / "high_school_book",
        "kind": "high_school",
        "repository": "litex-high-school-math",
    },
    "putnam_2025": {
        "title": "Putnam 2025 Litex",
        "source": "Putnam 2025",
        "path": SCRIPTS / "putnam_2025",
        "kind": "putnam_2025",
        "repository": "putnam_2025",
    },
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dataset",
        action="append",
        choices=sorted(DATASETS),
        help="Build only this dataset. Can be repeated.",
    )
    parser.add_argument(
        "--no-dashboard",
        action="store_true",
        help="Do not copy review.html into dataset workspaces.",
    )
    args = parser.parse_args()

    names = args.dataset or sorted(DATASETS)
    for name in names:
        config = DATASETS[name]
        workspace = config["path"]
        if not workspace.exists():
            raise FileNotFoundError(workspace)
        items = build_items(config)
        output = build_current_data(config, items)
        write_json(workspace / "current_data.json", output)
        if not args.no_dashboard:
            shutil.copyfile(TEMPLATE, workspace / "review.html")
        print(
            f"{name}: {len(items)} items -> "
            f"{workspace.relative_to(ROOT) / 'current_data.json'}"
        )


def build_items(config: dict[str, Any]) -> list[dict[str, Any]]:
    kind = config["kind"]
    if kind == "math500":
        return build_math500(config)
    if kind == "minif2f":
        return build_minif2f(config)
    if kind == "simple_jsonl":
        return build_simple_jsonl(config)
    if kind == "high_school":
        return build_high_school(config)
    if kind == "putnam_2025":
        return build_putnam_2025(config)
    raise ValueError(f"unknown dataset kind: {kind}")


def build_current_data(config: dict[str, Any], items: list[dict[str, Any]]) -> dict[str, Any]:
    summary = summarize(items)
    return {
        "schema_version": "litex-current-data/v1",
        "generated_at": dt.date.today().isoformat(),
        "dataset": {
            "id": dataset_id(config),
            "title": config["title"],
            "source": config["source"],
            "repository": config.get("repository", dataset_id(config)),
        },
        "status_legend": {
            "checkable": "Litex code is in a finished/checkable set or has documented verifier evidence.",
            "translated": "A Litex attempt exists, but this generator is not claiming fresh verification.",
            "blocked": "A translated or partial attempt is blocked by a known missing capability or proof debt.",
            "missing": "The source item is represented, but no Litex attempt is present yet.",
        },
        "contributor_flow": {
            "primary_queues": [
                "blocked",
                "missing",
                "needs_semantic_review",
                "needs_quality_review",
            ],
            "issue_title_template": f"[{dataset_id(config)}] <item id>: <task>",
            "pull_request_checklist": [
                "Update the source JSON/JSONL record and matching .lit file when one exists.",
                "Move solved items out of unfinished files and add a solved note when the workspace uses them.",
                "Run the smallest relevant Litex verifier command before marking an item checkable.",
                f"If working from the full golitex checkout, regenerate with: python3 scripts/build_dataset_current_data.py --dataset {dataset_id(config)}",
            ],
        },
        "summary": summary,
        "items": items,
    }


def build_math500(config: dict[str, Any]) -> list[dict[str, Any]]:
    workspace = config["path"]
    source_path = workspace / "litex_dataset" / "test-litex.jsonl"
    items: list[dict[str, Any]] = []
    for row_number, row in enumerate(read_jsonl(source_path), start=1):
        unique_id = row.get("unique_id") or f"row-{row_number:04d}"
        code = row.get("litex_code", "")
        flags = code_flags(code)
        if not has_claim_or_forall(code):
            flags.append("needs_semantic_review")
        status = "checkable"
        task = task_for(status, flags)
        litex_rel = Path("litex_file") / unique_id.replace(".json", ".lit")
        items.append(
            make_item(
                id=unique_id,
                source=config["source"],
                split="test",
                topic=row.get("subject", ""),
                difficulty=str(row.get("level", "")),
                problem=row.get("problem", ""),
                answer=row.get("answer", ""),
                natural_language_idea=first_text(row.get("solution", ""), 900),
                litex_code=code,
                proof_attempt="Verified release snippet in litex_code.",
                status=status,
                blocker="",
                notes="MATH-500 release item. Some checkable snippets are flagged for semantic-strengthening review.",
                flags=flags,
                contributor_task=task,
                paths={
                    "source_record": rel_to_workspace(source_path, workspace),
                    "litex_file": str(litex_rel),
                },
            )
        )
    return items


def build_minif2f(config: dict[str, Any]) -> list[dict[str, Any]]:
    workspace = config["path"]
    items: list[dict[str, Any]] = []
    specs = [
        ("finished", workspace / "litex_dataset" / "finished.jsonl", "checkable"),
        ("unfinished", workspace / "unfinished_dataset" / "unfinished.jsonl", "blocked"),
    ]
    for split, path, default_status in specs:
        if not path.exists():
            continue
        for row_number, row in enumerate(read_jsonl(path), start=1):
            name = row.get("name") or f"{split}-{row_number:04d}"
            code = row.get("litex_code", "")
            flags = code_flags(code)
            status = default_status
            blocker = extract_blocker(code)
            if default_status == "blocked" and not blocker:
                blocker = "blocked_by_stdlib"
            if default_status == "checkable" and flags:
                flags.append("needs_quality_review")
            task = task_for(status, flags)
            litex_dir = "litex_file" if split == "finished" else "unfinished_litex_file"
            items.append(
                make_item(
                    id=name,
                    source=config["source"],
                    split=split,
                    topic=infer_minif2f_topic(name),
                    difficulty=infer_minif2f_difficulty(name),
                    problem=clean_informal_prefix(row.get("informal_prefix", "")),
                    answer="",
                    natural_language_idea=extract_natural_idea(code),
                    litex_code=code,
                    proof_attempt="See litex_code for the current Litex proof attempt.",
                    status=status,
                    blocker=blocker,
                    notes=notes_for_minif2f(split, flags),
                    flags=flags,
                    contributor_task=task,
                    paths={
                        "source_record": rel_to_workspace(path, workspace),
                        "litex_file": f"{litex_dir}/{name}.lit",
                    },
                )
            )
    return items


def build_simple_jsonl(config: dict[str, Any]) -> list[dict[str, Any]]:
    workspace = config["path"]
    items: list[dict[str, Any]] = []
    seen: dict[str, int] = {}
    for split, rel_path, default_status in config["files"]:
        path = workspace / rel_path
        if not path.exists():
            continue
        for row_number, row in enumerate(read_jsonl(path), start=1):
            title = row.get("title") or row.get("name") or f"{split}-{row_number:06d}"
            item_id = unique_item_id(title, seen)
            code = row.get("litex_code") or row.get("solution") or ""
            flags = code_flags(code)
            status = default_status
            if status == "blocked":
                flags.append("unfinished_record")
            if not code.strip():
                status = "missing"
                flags.append("missing_litex_code")
            blocker = extract_blocker(code)
            if status == "blocked" and not blocker:
                blocker = "blocked_by_formulation"
            task = task_for(status, flags)
            description = row.get("description", "")
            problem = extract_question(description) or row.get("problem", "") or description
            answer = row.get("answer", "") or extract_answer(description)
            items.append(
                make_item(
                    id=item_id,
                    source=config["source"],
                    split=split,
                    topic=config.get("topic", ""),
                    difficulty="",
                    problem=problem,
                    answer=answer,
                    natural_language_idea=extract_solution_text(description),
                    litex_code=code,
                    proof_attempt="Litex-aligned code from the source row; fresh verification is not claimed here.",
                    status=status,
                    blocker=blocker,
                    notes="Generated from the current Litex-aligned JSONL split.",
                    flags=flags,
                    contributor_task=task,
                    paths={"source_record": rel_to_workspace(path, workspace)},
                )
            )
    return items


def build_high_school(config: dict[str, Any]) -> list[dict[str, Any]]:
    workspace = config["path"]
    verification = read_high_school_verification(workspace)
    items: list[dict[str, Any]] = []
    for path in sorted(workspace.glob("*_questions.json")):
        split = path.stem.replace("_questions", "")
        rows = read_json(path)
        for index, row in enumerate(rows, start=1):
            question = row.get("question", "")
            code = row.get("litex_code", "")
            flags = code_flags(code)
            item_id = f"{split}/{index:04d}"
            evidence = verification.get(item_id)
            if not question.strip():
                flags.append("empty_question_text")
            status = "translated" if code.strip() else "missing"
            if status == "missing":
                flags.append("missing_litex_code")
            if code.strip() and evidence:
                if (
                    evidence.get("status") == "checkable"
                    and evidence.get("code_sha256") == code_sha256(code)
                ):
                    status = "checkable"
                else:
                    flags.append("stale_verification_evidence")
            if code.strip() and not has_claim_or_forall(code):
                flags.append("needs_semantic_review")
            litex_rel = f"{split}_questions/{index:04d}.lit"
            proof_attempt = "High-school JSON litex_code field; fresh verification is not claimed here."
            notes = "Empty code means this item is ready for a first Litex translation."
            if status == "checkable" and evidence:
                proof_attempt = evidence.get("verified_command", proof_attempt)
                notes = evidence.get("notes", "Matched verifier evidence for this Litex code.")
            items.append(
                make_item(
                    id=item_id,
                    source=config["source"],
                    split=split,
                    topic=row.get("chapter", ""),
                    difficulty="required" if split.startswith("required") else "optional",
                    problem=question,
                    answer=row.get("answer", ""),
                    natural_language_idea=first_text(row.get("answer", ""), 600),
                    litex_code=code,
                    proof_attempt=proof_attempt,
                    status=status,
                    blocker="",
                    notes=notes,
                    flags=flags,
                    contributor_task=task_for(status, flags),
                    paths={
                        "source_record": rel_to_workspace(path, workspace),
                        "litex_file": litex_rel,
                    },
                )
            )
    return items


def build_putnam_2025(config: dict[str, Any]) -> list[dict[str, Any]]:
    workspace = config["path"]
    inventory = workspace / "dataset" / "problem_inventory.md"
    problems = parse_putnam_inventory(inventory)
    items: list[dict[str, Any]] = []
    for problem_id, problem_text in problems:
        status = "missing"
        code = ""
        blocker = ""
        flags = ["missing_litex_code"]
        notes = "Inventory item only; no Litex translation has been started."
        litex_file = ""
        if problem_id == "A2":
            partial = workspace / "unfinished_litex_file" / "A2_partial.lit"
            code = partial.read_text(encoding="utf-8") if partial.exists() else ""
            status = "blocked"
            blocker = "blocked_by_stdlib"
            flags = code_flags(code) + ["unfinished_record"]
            notes = "First slice item; partial Litex formulation is blocked by interval/trigonometric inequality support."
            litex_file = "unfinished_litex_file/A2_partial.lit"
        items.append(
            make_item(
                id=problem_id,
                source=config["source"],
                split="2025",
                topic="Putnam problem",
                difficulty="hard",
                problem=problem_text,
                answer="",
                natural_language_idea="",
                litex_code=code,
                proof_attempt="See unfinished_litex_file for A2; other items are inventory-only.",
                status=status,
                blocker=blocker,
                notes=notes,
                flags=flags,
                contributor_task=task_for(status, flags),
                paths={
                    "source_record": rel_to_workspace(inventory, workspace),
                    "litex_file": litex_file,
                },
            )
        )
    return items


def make_item(**kwargs: Any) -> dict[str, Any]:
    code = kwargs.get("litex_code", "")
    item = {
        "id": kwargs["id"],
        "source": kwargs["source"],
        "split": kwargs.get("split", ""),
        "topic": kwargs.get("topic", ""),
        "difficulty": kwargs.get("difficulty", ""),
        "natural_language_idea": kwargs.get("natural_language_idea", ""),
        "problem": kwargs.get("problem", ""),
        "answer": kwargs.get("answer", ""),
        "litex_code": code,
        "proof_attempt": kwargs.get("proof_attempt", ""),
        "status": kwargs["status"],
        "blocker": kwargs.get("blocker", ""),
        "flags": sorted(set(kwargs.get("flags", []))),
        "contributor_task": kwargs["contributor_task"],
        "notes": kwargs.get("notes", ""),
        "paths": {key: value for key, value in kwargs.get("paths", {}).items() if value},
    }
    item["item_hash"] = short_hash(
        "\0".join([item["id"], item["status"], item["litex_code"], item["notes"]])
    )
    return item


def summarize(items: list[dict[str, Any]]) -> dict[str, Any]:
    by_status = count_by(items, "status")
    by_task = count_by(items, "contributor_task")
    by_topic = count_by(items, "topic", limit=40)
    by_flag: dict[str, int] = {}
    for item in items:
        for flag in item.get("flags", []):
            by_flag[flag] = by_flag.get(flag, 0) + 1
    needs_review = sum(
        1
        for item in items
        if item.get("status") in {"blocked", "missing"}
        or any(is_review_flag(flag) for flag in item.get("flags", []))
    )
    return {
        "total_items": len(items),
        "checkable": by_status.get("checkable", 0),
        "translated": by_status.get("translated", 0),
        "blocked": by_status.get("blocked", 0),
        "missing": by_status.get("missing", 0),
        "needs_review": needs_review,
        "by_status": by_status,
        "by_contributor_task": by_task,
        "by_flag": dict(sorted(by_flag.items())),
        "top_topics": by_topic,
        "priority_ids": {
            "blocked": first_ids(items, "blocked"),
            "missing": first_ids(items, "missing"),
            "needs_semantic_review": first_ids_with_flag(items, "needs_semantic_review"),
            "needs_quality_review": first_ids_with_flag(items, "needs_quality_review"),
        },
    }


def task_for(status: str, flags: list[str]) -> str:
    if status == "blocked":
        return "repair_blocked"
    if status == "missing":
        return "write_translation"
    if "needs_semantic_review" in flags:
        return "semantic_review"
    if "needs_quality_review" in flags or "contains_know" in flags or "contains_abstract_prop" in flags:
        return "quality_review"
    if status == "translated":
        return "verify_or_audit"
    return "human_review"


def code_flags(code: str) -> list[str]:
    flags: list[str] = []
    if "know:" in code or re.search(r"\bknow\b", code):
        flags.append("contains_know")
    if "abstract_prop" in code:
        flags.append("contains_abstract_prop")
    if not code.strip():
        flags.append("missing_litex_code")
    return flags


def has_claim_or_forall(code: str) -> bool:
    return bool(re.search(r"(?m)^\s*(claim:|forall\b)", code))


def is_review_flag(flag: str) -> bool:
    return (
        flag.startswith("needs_")
        or flag in {
            "contains_know",
            "contains_abstract_prop",
            "empty_question_text",
            "stale_verification_evidence",
            "unfinished_record",
        }
    )


def extract_blocker(*texts: str) -> str:
    merged = "\n".join(text for text in texts if text)
    for label in BLOCKER_LABELS:
        if label in merged:
            return label
    return ""


def extract_natural_idea(code: str) -> str:
    lines = code.splitlines()
    collected: list[str] = []
    active = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("# Natural-language idea:"):
            active = True
            tail = stripped.removeprefix("# Natural-language idea:").strip()
            if tail:
                collected.append(tail)
            continue
        if active:
            if not stripped.startswith("#"):
                break
            text = stripped[1:].strip()
            if not text:
                if collected:
                    break
                continue
            collected.append(text)
    return first_text(" ".join(collected), 800)


def infer_minif2f_topic(name: str) -> str:
    lowered = name.lower()
    if "numbertheory" in lowered or "dvd" in lowered or "prime" in lowered:
        return "number theory"
    if "algebra" in lowered or "amgm" in lowered:
        return "algebra"
    if "induction" in lowered:
        return "induction"
    if "geometry" in lowered:
        return "geometry"
    if lowered.startswith("imo"):
        return "olympiad"
    if lowered.startswith("aime") or lowered.startswith("amc"):
        return "contest"
    if lowered.startswith("mathd"):
        return "mathd"
    return "miniF2F"


def infer_minif2f_difficulty(name: str) -> str:
    lowered = name.lower()
    if lowered.startswith("imo"):
        return "hard"
    if lowered.startswith("aime"):
        return "medium-hard"
    if lowered.startswith("amc"):
        return "medium"
    return ""


def notes_for_minif2f(split: str, flags: list[str]) -> str:
    if split == "unfinished":
        return "Unfinished MiniF2F item. Use the blocker label and partial Litex attempt as the starting point."
    if flags:
        return "Finished/checkable split item with review flags from the current_data generator."
    return "Finished/checkable MiniF2F item."


def clean_informal_prefix(text: str) -> str:
    text = text.strip()
    text = re.sub(r"^/--\s*", "", text)
    text = re.sub(r"-/\s*$", "", text)
    return text.strip()


def extract_question(description: str) -> str:
    if not description:
        return ""
    match = re.search(r"Question:\s*(.*?)(?:\nSolution:|\nAnswer:|\n####|\Z)", description, re.S)
    return match.group(1).strip() if match else ""


def extract_solution_text(description: str) -> str:
    match = re.search(r"Solution:\s*(.*?)(?:\nAnswer:|\n####|\Z)", description, re.S)
    return first_text(match.group(1), 900) if match else ""


def extract_answer(description: str) -> str:
    if not description:
        return ""
    patterns = [
        r"Answer:\s*(.*)",
        r"####\s*(.*)",
        r"The answer is:\s*(.*)",
    ]
    for pattern in patterns:
        matches = re.findall(pattern, description)
        if matches:
            return first_text(matches[-1].strip(), 300)
    return ""


def parse_putnam_inventory(path: Path) -> list[tuple[str, str]]:
    problems: list[tuple[str, str]] = []
    current_id = ""
    current_lines: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"- ([AB][1-6]):\s*(.*)", line)
        if match:
            if current_id:
                problems.append((current_id, " ".join(current_lines).strip()))
            current_id = match.group(1)
            current_lines = [match.group(2).strip()]
            continue
        if current_id and (line.startswith("  ") or line.startswith("\t")):
            current_lines.append(line.strip())
    if current_id:
        problems.append((current_id, " ".join(current_lines).strip()))
    return problems


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as error:
                raise ValueError(f"{path}:{line_number}: {error}") from error
    return rows


def read_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def read_high_school_verification(workspace: Path) -> dict[str, dict[str, Any]]:
    path = workspace / "verification_evidence.json"
    if not path.exists():
        return {}
    raw = read_json(path)
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected object keyed by high-school item id")
    evidence: dict[str, dict[str, Any]] = {}
    for item_id, value in raw.items():
        if not isinstance(value, dict):
            raise ValueError(f"{path}: expected evidence object for {item_id}")
        evidence[str(item_id)] = value
    return evidence


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def count_by(items: list[dict[str, Any]], key: str, limit: int | None = None) -> dict[str, int]:
    counts: dict[str, int] = {}
    for item in items:
        value = item.get(key) or "unknown"
        counts[value] = counts.get(value, 0) + 1
    sorted_counts = sorted(counts.items(), key=lambda pair: (-pair[1], pair[0]))
    if limit is not None:
        sorted_counts = sorted_counts[:limit]
    return dict(sorted_counts)


def first_ids(items: list[dict[str, Any]], status: str, limit: int = 50) -> list[str]:
    return [item["id"] for item in items if item.get("status") == status][:limit]


def first_ids_with_flag(items: list[dict[str, Any]], flag: str, limit: int = 50) -> list[str]:
    return [item["id"] for item in items if flag in item.get("flags", [])][:limit]


def first_text(text: str, limit: int) -> str:
    text = re.sub(r"\s+", " ", text or "").strip()
    if len(text) <= limit:
        return text
    return text[: limit - 3].rstrip() + "..."


def short_hash(text: str) -> str:
    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:12]


def code_sha256(code: str) -> str:
    return hashlib.sha256(code.encode("utf-8")).hexdigest()


def unique_item_id(raw_id: str, seen: dict[str, int]) -> str:
    base = str(raw_id).strip() or "item"
    count = seen.get(base, 0) + 1
    seen[base] = count
    return base if count == 1 else f"{base}#{count}"


def dataset_id(config: dict[str, Any]) -> str:
    for key, value in DATASETS.items():
        if value is config:
            return key
    return config["path"].name


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def rel_to_workspace(path: Path, workspace: Path) -> str:
    return str(path.relative_to(workspace))


if __name__ == "__main__":
    main()
