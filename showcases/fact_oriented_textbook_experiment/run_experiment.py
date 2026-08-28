#!/usr/bin/env python3
"""Validate and summarize the fact-oriented textbook annotation pilot."""

from __future__ import annotations

import argparse
import csv
import sys
import unicodedata
from collections import Counter
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, Sequence


LABELS = ("F", "H", "FH", "E")
REQUIRED_COLUMNS = (
    "unit_id",
    "slice_id",
    "stratum",
    "source_path",
    "start_line",
    "end_line",
    "cue",
    "label",
    "rationale",
)


class AnnotationError(ValueError):
    """Raised when an annotation file violates the showcase contract."""


@dataclass(frozen=True)
class Annotation:
    unit_id: str
    slice_id: str
    stratum: str
    source_path: str
    start_line: int
    end_line: int
    cue: str
    label: str
    rationale: str


@dataclass(frozen=True)
class Summary:
    counts: Counter[str]
    total: int
    proof_relevant: int
    fact_lower: float
    fact_midpoint: float
    fact_upper: float
    how_lower: float
    how_midpoint: float
    how_upper: float


def load_annotations(path: Path) -> list[Annotation]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise AnnotationError("annotation file has no header")
        missing = [name for name in REQUIRED_COLUMNS if name not in reader.fieldnames]
        if missing:
            raise AnnotationError(f"missing columns: {', '.join(missing)}")

        annotations: list[Annotation] = []
        seen_ids: set[str] = set()
        for row_number, row in enumerate(reader, start=2):
            unit_id = row["unit_id"].strip()
            if not unit_id:
                raise AnnotationError(f"row {row_number}: empty unit_id")
            if unit_id in seen_ids:
                raise AnnotationError(f"row {row_number}: duplicate unit_id {unit_id!r}")
            seen_ids.add(unit_id)

            label = row["label"].strip()
            if label not in LABELS:
                raise AnnotationError(
                    f"row {row_number}: invalid label {label!r}; expected one of {LABELS}"
                )

            try:
                start_line = int(row["start_line"])
                end_line = int(row["end_line"])
            except ValueError as error:
                raise AnnotationError(
                    f"row {row_number}: line bounds must be integers"
                ) from error
            if start_line < 1 or end_line < start_line:
                raise AnnotationError(
                    f"row {row_number}: invalid line range {start_line}-{end_line}"
                )

            source_path = row["source_path"].strip()
            posix_path = PurePosixPath(source_path)
            if not source_path or posix_path.is_absolute() or ".." in posix_path.parts:
                raise AnnotationError(
                    f"row {row_number}: source_path must be repository-relative"
                )

            cue = row["cue"].strip()
            if not cue:
                raise AnnotationError(f"row {row_number}: empty cue")
            if len(cue.split()) > 12:
                raise AnnotationError(
                    f"row {row_number}: cue exceeds the 12-word quotation limit"
                )

            slice_id = row["slice_id"].strip()
            stratum = row["stratum"].strip()
            rationale = row["rationale"].strip()
            if not slice_id or not stratum or not rationale:
                raise AnnotationError(
                    f"row {row_number}: slice_id, stratum, and rationale are required"
                )

            annotations.append(
                Annotation(
                    unit_id=unit_id,
                    slice_id=slice_id,
                    stratum=stratum,
                    source_path=source_path,
                    start_line=start_line,
                    end_line=end_line,
                    cue=cue,
                    label=label,
                    rationale=rationale,
                )
            )

    if not annotations:
        raise AnnotationError("annotation file contains no rows")
    return annotations


def normalize_text(value: str) -> str:
    return " ".join(unicodedata.normalize("NFKC", value).casefold().split())


def validate_sources(annotations: Iterable[Annotation], repository_root: Path) -> None:
    source_cache: dict[str, list[str]] = {}
    for annotation in annotations:
        if annotation.source_path not in source_cache:
            source = repository_root / annotation.source_path
            if not source.is_file():
                raise AnnotationError(
                    f"{annotation.unit_id}: source does not exist: {annotation.source_path}"
                )
            # Source references use the same newline model as `nl -ba`.  Python's
            # splitlines() also treats form-feed page markers as boundaries, which
            # would silently shift every line number after the first PDF page.
            source_cache[annotation.source_path] = source.read_text(
                encoding="utf-8"
            ).split("\n")

        lines = source_cache[annotation.source_path]
        if annotation.end_line > len(lines):
            raise AnnotationError(
                f"{annotation.unit_id}: line {annotation.end_line} exceeds source length {len(lines)}"
            )
        source_span = " ".join(
            lines[annotation.start_line - 1 : annotation.end_line]
        )
        if normalize_text(annotation.cue) not in normalize_text(source_span):
            raise AnnotationError(
                f"{annotation.unit_id}: cue not found in lines "
                f"{annotation.start_line}-{annotation.end_line}"
            )


def summarize(annotations: Sequence[Annotation]) -> Summary:
    counts = Counter(annotation.label for annotation in annotations)
    total = len(annotations)
    proof_relevant = counts["F"] + counts["H"] + counts["FH"]
    if proof_relevant == 0:
        return Summary(
            counts=counts,
            total=total,
            proof_relevant=0,
            fact_lower=0.0,
            fact_midpoint=0.0,
            fact_upper=0.0,
            how_lower=0.0,
            how_midpoint=0.0,
            how_upper=0.0,
        )

    denominator = float(proof_relevant)
    return Summary(
        counts=counts,
        total=total,
        proof_relevant=proof_relevant,
        fact_lower=counts["F"] / denominator,
        fact_midpoint=(counts["F"] + 0.5 * counts["FH"]) / denominator,
        fact_upper=(counts["F"] + counts["FH"]) / denominator,
        how_lower=counts["H"] / denominator,
        how_midpoint=(counts["H"] + 0.5 * counts["FH"]) / denominator,
        how_upper=(counts["H"] + counts["FH"]) / denominator,
    )


def percentage(value: float) -> str:
    return f"{100.0 * value:.1f}%"


def render_report(annotations: Sequence[Annotation]) -> str:
    overall = summarize(annotations)
    lines = [
        "# Analysis I Pilot Results",
        "",
        "This file is generated from `annotations/pilot_analysis_i.csv` by",
        "`run_experiment.py`. The three slices are purposive contrasts, not a",
        "probability sample of the book.",
        "",
        "## Overall label distribution",
        "",
        "| Label | Count | Share of all units |",
        "| --- | ---: | ---: |",
    ]
    for label in LABELS:
        lines.append(
            f"| {label} | {overall.counts[label]} | "
            f"{percentage(overall.counts[label] / overall.total)} |"
        )

    fact_bearing = (overall.counts["F"] + overall.counts["FH"]) / overall.total
    how_bearing = (overall.counts["H"] + overall.counts["FH"]) / overall.total
    lines.extend(
        [
            "",
            f"Total annotated units: **{overall.total}**.",
            "",
            f"Fact-bearing units (`F` or `FH`): **{percentage(fact_bearing)}**.  ",
            f"How-bearing units (`H` or `FH`): **{percentage(how_bearing)}**.  ",
            "These two bearing rates overlap because every `FH` unit belongs to both.",
            "",
            "## Sensitivity band among proof-relevant units",
            "",
            "`E` units are excluded here. The lower bound assigns every `FH` unit to",
            "the opposite side; the midpoint splits `FH` equally; the upper bound",
            "assigns every `FH` unit to the named side.",
            "",
            "| Orientation | Lower | Midpoint | Upper |",
            "| --- | ---: | ---: | ---: |",
            f"| Fact | {percentage(overall.fact_lower)} | "
            f"{percentage(overall.fact_midpoint)} | {percentage(overall.fact_upper)} |",
            f"| How | {percentage(overall.how_lower)} | "
            f"{percentage(overall.how_midpoint)} | {percentage(overall.how_upper)} |",
            "",
            "## Slice contrast",
            "",
            "| Slice | Stratum | Units | F | H | FH | E | Fact midpoint | How midpoint |",
            "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
    )

    slice_ids = list(dict.fromkeys(annotation.slice_id for annotation in annotations))
    for slice_id in slice_ids:
        subset = [
            annotation for annotation in annotations if annotation.slice_id == slice_id
        ]
        summary = summarize(subset)
        strata = {annotation.stratum for annotation in subset}
        stratum = next(iter(strata)) if len(strata) == 1 else "mixed"
        lines.append(
            f"| `{slice_id}` | {stratum} | {summary.total} | "
            f"{summary.counts['F']} | {summary.counts['H']} | "
            f"{summary.counts['FH']} | {summary.counts['E']} | "
            f"{percentage(summary.fact_midpoint)} | "
            f"{percentage(summary.how_midpoint)} |"
        )

    lines.extend(
        [
            "",
            "## What this pilot establishes",
            "",
            "The same rubric detects a sharp genre effect: the induction-proof tracer",
            "contains more explicit proof control than the definition and example",
            "slices. Mixed units are common enough that a forced binary count would",
            "hide material uncertainty.",
            "",
            "It does **not** estimate the whole book. A book-level result requires the",
            "probability sampling, double annotation, weighting, and clause-level",
            "sensitivity analysis specified in the README.",
            "",
        ]
    )
    return "\n".join(lines)


def default_repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def default_annotations_path() -> Path:
    return Path(__file__).resolve().parent / "annotations" / "pilot_analysis_i.csv"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--annotations", type=Path, default=default_annotations_path()
    )
    parser.add_argument(
        "--repository-root", type=Path, default=default_repository_root()
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("validate", help="validate schema and source references")
    report_parser = subparsers.add_parser("report", help="render the pilot report")
    report_parser.add_argument("--output", type=Path)
    report_parser.add_argument(
        "--check", type=Path, help="fail unless this file matches the rendered report"
    )
    args = parser.parse_args(argv)

    try:
        annotations = load_annotations(args.annotations)
        validate_sources(annotations, args.repository_root)
        if args.command == "validate":
            print(f"validated {len(annotations)} annotations")
            return 0

        report = render_report(annotations)
        if args.check is not None:
            if not args.check.is_file() or args.check.read_text(encoding="utf-8") != report:
                raise AnnotationError(f"generated report differs from {args.check}")
            print(f"report matches {args.check}")
            return 0
        if args.output is not None:
            args.output.write_text(report, encoding="utf-8")
            print(f"wrote {args.output}")
        else:
            print(report, end="")
        return 0
    except (AnnotationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
