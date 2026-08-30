#!/usr/bin/env python3
"""Validate recorded session events and materialize the accepted prefix."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_BLOCKS = (
    ("B001", False),
    ("B002", True),
    ("B003", True),
    ("B004", True),
)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def first_json_value(text: str) -> dict:
    value, _ = json.JSONDecoder().raw_decode(text)
    return value


def source_without_try(path: Path) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0] != "try:":
        raise ValueError(f"{path} does not begin with a literal outermost try")
    stripped = [line[4:] if line.startswith("    ") else line for line in lines[1:]]
    return "\n".join(stripped).rstrip() + "\n"


def validate_events(raw: bytes) -> list[dict]:
    events = [json.loads(line) for line in raw.splitlines()]
    if not events or events[0] != {"event": "ready", "mode": "project"}:
        raise ValueError("recording does not begin with the project ready event")
    actual = [(event.get("id"), event.get("ok")) for event in events[1:]]
    if actual != list(EXPECTED_BLOCKS):
        raise ValueError(f"unexpected block sequence: {actual}")
    failed_trace = first_json_value(events[1]["trace"])
    instantiate_error = failed_trace["previous_error"]["previous_error"]
    if instantiate_error != {
        "error_type": "InstantiateError",
        "result": "error",
        "message": "argument count mismatch: expected 4 parameter(s), got 3 argument(s)",
    }:
        raise ValueError(f"unexpected B001 diagnostic: {instantiate_error}")
    for event in events[2:]:
        trace_root = first_json_value(event["trace"])
        if trace_root.get("schema") != "litex.statement-result.v2":
            raise ValueError(f"{event['id']} is missing the v2 result schema")
        if trace_root.get("outcome") != "success":
            raise ValueError(f"{event['id']} did not report a successful trace")
    return events


def build_evidence(raw: bytes, events: list[dict], target: str) -> dict:
    projected = [{"event": "ready", "mode": "project"}]
    for event in events[1:]:
        trace_root = first_json_value(event["trace"])
        projection = {
            "event": event["event"],
            "id": event["id"],
            "ok": event["ok"],
            "trace_sha256": sha256_bytes(event["trace"].encode("utf-8")),
            "trace_bytes": len(event["trace"].encode("utf-8")),
        }
        if event["ok"]:
            projection["trace_root"] = {
                "schema": trace_root["schema"],
                "outcome": trace_root["outcome"],
                "result_kind": trace_root["result"]["kind"],
            }
        else:
            inner = trace_root["previous_error"]
            projection["decisive_trace_excerpt"] = {
                "outer_error_type": trace_root["error_type"],
                "failed_phase": "verify_well_definedness",
                "statement": inner["statement"],
                "message": inner["message"],
                "previous_error": inner["previous_error"],
            }
        projected.append(projection)
    return {
        "schema_version": 1,
        "recorded_on": "2026-08-29",
        "recorded_target": "tmp/2026-08-29/ai-litex-sylow-showcase/main.lit",
        "published_target": target,
        "recorded_session_command": "target/release/litex -compact -session -before tmp/2026-08-29/ai-litex-sylow-showcase/main.lit",
        "replay_session_command": f"target/release/litex -compact -session -before {target}",
        "raw_jsonl": {
            "sha256": sha256_bytes(raw),
            "bytes": len(raw),
            "publication": "Reproduce with replay_session.py; the full successful traces are intentionally kept out of the compact showcase evidence.",
        },
        "events": projected,
        "rollback_inference": "B002 successfully declares the same theorem name attempted by failed B001; therefore B001 did not leak that declaration. B003 then successfully cites the declaration committed by B002 without replaying it.",
    }


def build_journal(showcase_dir: Path, target: str) -> dict:
    failed = source_without_try(showcase_dir / "frame_01_failed.lit.txt")
    accepted_cardinality = source_without_try(showcase_dir / "frame_02_accepted.lit.txt")
    accepted_reuse = source_without_try(showcase_dir / "frame_03_reuse.lit.txt")
    accepted_endpoint = source_without_try(showcase_dir / "frame_04_endpoint.lit.txt")
    return {
        "schema_version": 1,
        "target": target,
        "session_command": f"target/release/litex -compact -session -before {target}",
        "proof_spine": [
            "Use the canonical coordinate-bijection theorem to obtain finiteness and the exact quotient-preimage cardinality.",
            "Substitute |K| = p and |H| = p^k to obtain the successor order p^(k+1).",
            "Cite the canonical exponent-induction theorem for the First Sylow endpoint.",
        ],
        "blocks": [
            {
                "id": "P001",
                "source_order": 1,
                "intent": "Expose the exact quotient-preimage cardinality checkpoint.",
                "dependencies": ["MIL::chap9::sylow_quotient_preimage_cardinality"],
                "attempts": [
                    {
                        "candidate": failed,
                        "result": "failed",
                        "verifier_evidence": "InstantiateError: argument count mismatch: expected 4 parameter(s), got 3 argument(s)",
                        "diagnosis": "The theorem release failed during well-definedness because K was omitted from the four-parameter interface.",
                        "next_change": "Pass K as the fourth theorem argument; keep the statement unchanged.",
                    },
                    {
                        "candidate": accepted_cardinality,
                        "result": "accepted",
                        "verifier_evidence": "session block B002 returned ok:true with litex.statement-result.v2 outcome success",
                        "diagnosis": "The corrected release matches the canonical theorem contract.",
                        "next_change": "Advance to the prime-power consumer.",
                    },
                ],
                "accepted_litex": accepted_cardinality,
                "reusable_lesson": "When a named theorem call fails before proof search, compare its exact arity and carrier contract before changing the mathematics.",
                "status": "materialized_pending_file_gate",
            },
            {
                "id": "P002",
                "source_order": 2,
                "intent": "Reuse the committed cardinality checkpoint and calculate the prime-power successor order.",
                "dependencies": ["P001", "quotient_preimage_cardinality_checkpoint"],
                "attempts": [
                    {
                        "candidate": accepted_reuse,
                        "result": "accepted",
                        "verifier_evidence": "session block B003 returned ok:true with litex.statement-result.v2 outcome success",
                        "diagnosis": "The prior successful frame is callable in the same Runtime and the equality chain closes the target.",
                        "next_change": "Advance to the First Sylow endpoint.",
                    }
                ],
                "accepted_litex": accepted_reuse,
                "reusable_lesson": "A successful outermost try commits its declaration; the next source block should cite it without replaying accepted source.",
                "status": "materialized_pending_file_gate",
            },
            {
                "id": "P003",
                "source_order": 3,
                "intent": "Connect the deep checkpoint to the complete First Sylow theorem.",
                "dependencies": ["MIL::chap9::p_power_subgroup_exists"],
                "attempts": [
                    {
                        "candidate": accepted_endpoint,
                        "result": "accepted",
                        "verifier_evidence": "session block B004 returned ok:true with litex.statement-result.v2 outcome success",
                        "diagnosis": "The endpoint exactly matches the canonical exponent-induction theorem.",
                        "next_change": "Materialize the contiguous accepted prefix and run the clean file gate.",
                    }
                ],
                "accepted_litex": accepted_endpoint,
                "reusable_lesson": "Keep the full theorem endpoint as one named interface after independently tracing its decisive internal node.",
                "status": "materialized_pending_file_gate",
            },
        ],
        "materialization": {
            "block_ids": ["P001", "P002", "P003"],
            "source_matches_frames": True,
            "file_gate_command": f"target/release/litex -compact -runner -f {target}",
            "file_gate_result": "not_run",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--events", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    showcase_dir = Path(__file__).resolve().parent
    raw = args.events.read_bytes()
    events = validate_events(raw)
    target = "showcases/ai_litex_sylow/main.lit"
    evidence = build_evidence(raw, events, target)
    journal = build_journal(showcase_dir, target)
    accepted = "\n".join(
        source_without_try(showcase_dir / name).rstrip()
        for name in (
            "frame_02_accepted.lit.txt",
            "frame_03_reuse.lit.txt",
            "frame_04_endpoint.lit.txt",
        )
    )
    materialized = (
        "# Materialized accepted prefix from proof_journal.json. The interactive frame\n"
        "# wrappers are intentionally absent from canonical source.\n\n"
        f"{accepted}\n"
    )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "main.lit").write_text(materialized, encoding="utf-8")
    (args.output_dir / "session_evidence.json").write_text(
        json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (args.output_dir / "proof_journal.json").write_text(
        json.dumps(journal, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps({"materialized": True, "blocks": ["P001", "P002", "P003"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
