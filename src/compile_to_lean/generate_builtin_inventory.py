#!/usr/bin/env python3
"""Generate the source-derived Litex-to-Lean builtin provenance inventory."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "src/compile_to_lean/builtin_rule_inventory.md"
SOURCE_ROOTS = [ROOT / "src/verify", ROOT / "src/execute"]
LOCAL_BUILTIN_CATALOG_ROOT = ROOT / "src/verify/local_builtin_catalog"
LOCAL_BUILTIN_RULE_COUNT = len(tuple(LOCAL_BUILTIN_CATALOG_ROOT.rglob("*.lit")))

# Function name -> (label argument index, provenance kind).
INITIAL_SINKS = {
    "new_with_verified_by_builtin_rules_recording_stmt": [(1, "rule")],
    "new_with_verified_by_builtin_rules_label_and_steps": [(2, "rule")],
    "new_with_verified_by_builtin_rule_evidence_and_steps": [(2, "rule")],
    "new_with_verified_by_builtin_rule_evidence_recording_stmt": [(1, "rule")],
    "new_with_verified_by_builtin_strategy_recording_stmt": [(1, "strategy")],
    "new_with_verified_by_builtin_strategy_evidence_recording_stmt": [(1, "strategy")],
}

ARITHMETIC_LEAN_MAPPINGS = {
    "less_equal_fact_from_known_strict_order": "`linarith only`",
    "greater_equal_fact_from_known_strict_order": "`linarith only`",
    "0 <= u - v from v <= u": "`linarith only`",
    "0 < u - v from v < u": "`linarith only`",
    "0 <= a + b from known atomic facts 0 <= a and 0 <= b": "`linarith only`",
    "0 < a + b from 0 < a and 0 < b": "`linarith only`",
    "0 < a + b from (0 < a and 0 <= b)": "`linarith only`",
    "0 < a + b from (0 <= a and 0 < b)": "`linarith only`",
    "0 <= a * b from 0 <= a and 0 <= b": "`mul_nonneg`",
    "0 < a * b from 0 < a and 0 < b": "`mul_pos`",
    "0 <= a / b from 0 <= a and 0 < b": "`div_nonneg` + `le_of_lt`",
    "0 < a / b from 0 < a and 0 < b": "`div_pos`",
    "u + a <= u + b from a <= b": "`linarith only`",
    "a - c <= b from a <= b and 0 <= c": "`linarith only`",
    "a <= a + b from 0 <= b": "`linarith only`",
    "a + c <= b + d from a <= b and c <= d": "`linarith only`",
    "u + a < u + b from a < b": "`linarith only`",
    "a + c < b + d from a < b and c < d": "`linarith only`",
    "a + c < b + d from a < b and c <= d": "`linarith only`",
    "a + c < b + d from a <= b and c < d": "`linarith only`",
}

SET_AND_ABSOLUTE_VALUE_LEAN_MAPPINGS = {
    "union_commutative": "`ext x; simp [or_comm]`",
    "union_associative": "`ext x; simp [or_assoc]`",
    "union_idempotent": "`ext x; simp`",
    "union_empty_identity": "`ext x; simp`",
    "intersect_commutative": "`ext x; simp [and_comm]`",
    "intersect_associative": "`ext x; simp [and_assoc]`",
    "intersection membership: member of both sides": "`Set.mem_inter_iff` + pair",
    "set-minus membership: member of left side and non-member of right side": "`Set.mem_diff` + pair",
    "abs: abs(x) = x from 0 <= x": "`abs_of_nonneg`",
    "abs: abs(x) = -x from x <= 0": "`abs_of_nonpos`",
    "abs: abs(x * y) = abs(x) * abs(y)": "`abs_mul`",
    "abs: 0 < abs(x) from x != 0": "`abs_pos.mpr`",
}

EVALUATION_MARKERS = (
    "calculation",
    "computation",
    "computed",
    "evaluate",
    "evaluated",
    "evaluation",
    "literal",
    "constant fold",
    "core value",
    "closed numeric",
    "numeric normalization",
)

TYPED_LOCAL_RULE_SINKS = {
    "new_with_verified_by_builtin_rule_evidence_and_steps",
    "new_with_verified_by_builtin_rule_evidence_recording_stmt",
}

TRANSFORM_FUNCTION_MARKERS = (
    "duality",
    "rewrite",
    "symmetr",
    "transpose",
    "transport",
)

QUANTIFIED_FUNCTION_MARKERS = (
    "enumerate",
    "forall",
    "induc",
    "pointwise",
    "replacement",
)


def rust_files() -> list[Path]:
    files: list[Path] = []
    for source_root in SOURCE_ROOTS:
        files.extend(source_root.rglob("*.rs"))
    return sorted(files)


def skip_quoted(source: str, index: int) -> int | None:
    raw = re.match(r"(?:b)?r(#{0,16})\"", source[index:])
    if raw:
        hashes = raw.group(1)
        end_marker = '"' + hashes
        content_start = index + raw.end()
        end = source.find(end_marker, content_start)
        return len(source) if end < 0 else end + len(end_marker)

    byte_prefix = source.startswith('b"', index)
    if source.startswith('"', index) or byte_prefix:
        cursor = index + (2 if byte_prefix else 1)
        while cursor < len(source):
            if source[cursor] == "\\":
                cursor += 2
            elif source[cursor] == '"':
                return cursor + 1
            else:
                cursor += 1
        return len(source)

    if source.startswith("'", index):
        cursor = index + 1
        if cursor < len(source) and source[cursor] == "\\":
            cursor += 2
        else:
            cursor += 1
        if cursor < len(source) and source[cursor] == "'":
            return cursor + 1
    return None


def skip_comment(source: str, index: int) -> int | None:
    if source.startswith("//", index):
        end = source.find("\n", index + 2)
        return len(source) if end < 0 else end + 1
    if source.startswith("/*", index):
        depth = 1
        cursor = index + 2
        while cursor < len(source) and depth:
            if source.startswith("/*", cursor):
                depth += 1
                cursor += 2
            elif source.startswith("*/", cursor):
                depth -= 1
                cursor += 2
            else:
                cursor += 1
        return cursor
    return None


def balanced(source: str, opening: int) -> tuple[list[str], int] | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    if source[opening] not in pairs:
        return None
    stack = [pairs[source[opening]]]
    args: list[str] = []
    argument_start = opening + 1
    cursor = opening + 1
    while cursor < len(source):
        skipped = skip_comment(source, cursor)
        if skipped is None:
            skipped = skip_quoted(source, cursor)
        if skipped is not None:
            cursor = skipped
            continue
        character = source[cursor]
        if character in pairs:
            stack.append(pairs[character])
        elif stack and character == stack[-1]:
            stack.pop()
            if not stack:
                tail = source[argument_start:cursor].strip()
                if tail or args:
                    args.append(tail)
                return args, cursor + 1
        elif character == "," and len(stack) == 1 and stack[-1] == ")":
            args.append(source[argument_start:cursor].strip())
            argument_start = cursor + 1
        cursor += 1
    return None


def find_calls(source: str, name: str, start: int = 0, end: int | None = None):
    limit = len(source) if end is None else end
    pattern = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(name)}\s*\(")
    for match in pattern.finditer(source, start, limit):
        prefix = source[max(start, match.start() - 12) : match.start()]
        if re.search(r"\bfn\s+$", prefix):
            continue
        opening = source.find("(", match.start(), match.end())
        parsed = balanced(source, opening)
        if parsed is None:
            continue
        args, call_end = parsed
        if call_end <= limit:
            yield match.start(), call_end, args


def split_parameters(source: str) -> list[str]:
    wrapped = "(" + source + ")"
    parsed = balanced(wrapped, 0)
    if parsed is None:
        return []
    names: list[str] = []
    for parameter in parsed[0]:
        before_type = parameter.split(":", 1)[0].strip()
        before_type = before_type.removeprefix("mut ").strip()
        before_type = before_type.lstrip("&").removeprefix("mut ").strip()
        name = before_type.split()[-1] if before_type else ""
        if name and name != "self":
            names.append(name)
    return names


def function_ranges(source: str):
    functions = []
    pattern = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")
    for match in pattern.finditer(source):
        opening = source.find("(", match.end())
        if opening < 0:
            continue
        parameters = balanced(source, opening)
        if parameters is None:
            continue
        parameter_args, after_parameters = parameters
        cursor = after_parameters
        body_opening = -1
        while cursor < len(source):
            skipped = skip_comment(source, cursor)
            if skipped is None:
                skipped = skip_quoted(source, cursor)
            if skipped is not None:
                cursor = skipped
                continue
            if source[cursor] == ";":
                break
            if source[cursor] == "{":
                body_opening = cursor
                break
            cursor += 1
        if body_opening < 0:
            continue
        body = balanced(source, body_opening)
        if body is None:
            continue
        _, body_end = body
        raw_parameters = source[opening + 1 : after_parameters - 1]
        functions.append(
            {
                "name": match.group(1),
                "params": split_parameters(raw_parameters),
                "start": match.start(),
                "body_start": body_opening + 1,
                "end": body_end,
            }
        )
    return functions


def forwarded_parameter(expression: str, parameters: list[str]) -> int | None:
    compact = re.sub(r"\s+", "", expression)
    compact = compact.removeprefix("&")
    for suffix in (".to_string()", ".clone()", ".as_str()"):
        if compact.endswith(suffix):
            compact = compact[: -len(suffix)]
    for index, parameter in enumerate(parameters):
        if compact == parameter:
            return index
    return None


def discover_sinks(sources, functions_by_path):
    sinks = dict(INITIAL_SINKS)
    changed = True
    while changed:
        changed = False
        for path, source in sources.items():
            for function in functions_by_path[path]:
                for sink_name, routes in list(sinks.items()):
                    for label_index, kind in routes:
                        for _, _, args in find_calls(
                            source,
                            sink_name,
                            function["body_start"],
                            function["end"],
                        ):
                            if label_index >= len(args):
                                continue
                            parameter_index = forwarded_parameter(
                                args[label_index], function["params"]
                            )
                            if parameter_index is None:
                                continue
                            candidate = (parameter_index, kind)
                            function_routes = sinks.setdefault(function["name"], [])
                            if candidate not in function_routes:
                                function_routes.append(candidate)
                                function_routes.sort()
                                changed = True
    return sinks


def enclosing_function(functions, offset: int):
    candidates = [item for item in functions if item["start"] <= offset < item["end"]]
    return max(candidates, key=lambda item: item["start"], default=None)


def compact_expression(expression: str) -> str:
    return " ".join(expression.split())


def static_label(expression: str) -> str | None:
    compact = compact_expression(expression)
    match = re.fullmatch(
        r'"((?:\\.|[^"\\])*)"(?:\s*\.\s*(?:to_string|into)\(\))?', compact
    )
    if match:
        return match.group(1).replace(r'\"', '"').replace(r"\\", "\\")
    return None


def inventory_entries(sources, functions_by_path, sinks):
    entries = []
    seen = set()
    for path, source in sources.items():
        functions = functions_by_path[path]
        for sink_name, routes in sinks.items():
            for label_index, kind in routes:
                for offset, _, args in find_calls(source, sink_name):
                    if label_index >= len(args):
                        continue
                    function = enclosing_function(functions, offset)
                    if function is not None:
                        parameter_index = forwarded_parameter(
                            args[label_index], function["params"]
                        )
                        wrapper_routes = sinks.get(function["name"], [])
                        if parameter_index is not None and (
                            parameter_index,
                            kind,
                        ) in wrapper_routes:
                            continue
                    key = (path, offset, label_index, kind)
                    if key in seen:
                        continue
                    seen.add(key)
                    expression = compact_expression(args[label_index])
                    label = static_label(expression)
                    entries.append(
                        {
                            "path": path.relative_to(ROOT).as_posix(),
                            "line": source.count("\n", 0, offset) + 1,
                            "kind": kind,
                            "sink": sink_name,
                            "expression": expression,
                            "label": label,
                            "function": function["name"] if function is not None else None,
                        }
                    )
    entries.sort(key=lambda item: (item["path"], item["line"], item["expression"]))
    return entries


def family(entry) -> str:
    path = entry["path"]
    if "verify_builtin_strategies/" in path:
        return "builtin strategy"
    if "equality_numeric/" in path:
        return "numeric equality"
    if "in_fact_builtin/" in path:
        return "membership"
    if path.startswith("src/execute/"):
        return "execution bridge"
    stem = Path(path).stem.replace("_", " ")
    return stem.removeprefix("verify ").removesuffix(" builtin")


def is_evaluation(entry) -> bool:
    text = (entry["label"] or entry["expression"]).lower()
    path = entry["path"]
    if path.endswith("prime_builtin.rs") or path.endswith("in_fact_builtin/numeric_values.rs"):
        return True
    if "trusted file load" in text:
        return True
    return any(marker in text for marker in EVALUATION_MARKERS)


def mechanism_class(entry) -> str:
    """Conservatively classify the executable proof mechanism at a site.

    The classifier follows the sink, enclosing function, and source family;
    diagnostic labels are not semantic identities. Mixed or unaudited routes
    remain ``legacy_custom`` until they are migrated or classified explicitly.
    """

    if entry["kind"] == "strategy":
        return "strategy"
    if is_evaluation(entry) and "trusted file load" not in (
        entry["label"] or entry["expression"]
    ).lower():
        return "reflection"

    path = entry["path"]
    function = (entry.get("function") or "").lower()
    function_without_negative_forall = function.replace("non_forall", "")
    if "by_definition" in path or "definition" in function:
        return "definition"
    if any(marker in function for marker in TRANSFORM_FUNCTION_MARKERS):
        return "transform"
    if any(
        marker in function_without_negative_forall
        for marker in QUANTIFIED_FUNCTION_MARKERS
    ):
        return "quantified"
    if function == "verify_in_fact_by_known_standard_subset_membership":
        return "transform"
    if entry["sink"] in TYPED_LOCAL_RULE_SINKS:
        return "local_schema"
    return "legacy_custom"


def lean_mapping(entry) -> tuple[str, str]:
    text = entry["label"] or entry["expression"]
    if entry["path"].endswith("verify/local_builtin_catalog/verify.rs"):
        return (
            f"paired Litex schema + checked Lean adapter ({LOCAL_BUILTIN_RULE_COUNT} RuleIds)",
            "implemented",
        )
    direct_mapping = SET_AND_ABSOLUTE_VALUE_LEAN_MAPPINGS.get(text)
    if direct_mapping is not None:
        return direct_mapping, "implemented"
    if entry["path"].endswith("in_fact_builtin/set_membership.rs"):
        if "union membership: member of the" in text:
            return "`Set.mem_union` + `Or.inl`/`Or.inr`", "implemented"
        if "intersection non-membership: non-member of the" in text:
            return "`Set.mem_inter_iff` + contradiction", "implemented"
    if (
        entry["sink"] == "new_with_verified_by_builtin_rule_evidence_and_steps"
        and text == "div_not_equal_zero_from_numerator_nonzero"
    ):
        return "`div_ne_zero` / `Ne.symm`", "implemented"
    if entry["sink"] == "new_with_verified_by_builtin_rule_evidence_recording_stmt":
        if text == "fn application in its exact instantiated declared return set":
            return (
                "exact source-layer elimination of retained function membership",
                "implemented",
            )
        if (
            text
            == "fn membership: same input domain and pointwise values lie in the target return set"
        ):
            return (
                "checked pointwise `forall` specialization into a native function-set predicate",
                "implemented",
            )
        if entry.get("function") == "verify_in_fact_by_known_standard_subset_membership":
            return (
                "native membership projection + checked numeric coercion",
                "implemented",
            )
        if text == "not-equality symmetry":
            return "`Ne.symm`", "implemented"
        if text == "subset_superset_duality":
            return "native subset proposition (one reversed checked premise)", "implemented"
        if text == "deterministic primality computation for u64":
            return "`Nat.Prime` / `norm_num`", "implemented"
        if text in (
            "integer expression closure under +, -, and *",
            "Z closure: binary integer arithmetic",
        ):
            return (
                "native `ℤ` membership with checked ordered operand proofs",
                "implemented",
            )
        mapping = ARITHMETIC_LEAN_MAPPINGS.get(text)
        if mapping is not None:
            return mapping, "implemented"
    if (
        entry["sink"]
        == "new_with_verified_by_builtin_strategy_evidence_recording_stmt"
    ):
        return "recursive typed arithmetic evidence (`linarith only`)", "implemented"
    if text in (
        "bounded symbolic normalization",
        "calculation and rational expression simplification",
    ):
        return "`norm_num` / `ring` / `field_simp; ring`", "implemented"
    if text == "standard_nonempty_set":
        return "existential witness `0` over `N/Z/Q/R/C`", "implemented"
    if is_evaluation(entry):
        return "none", "not_this_round"
    return "none", "pending"


def markdown(entries, sinks, raw_constructor_count: int) -> str:
    strategy_count = sum(item["kind"] == "strategy" for item in entries)
    rule_count = len(entries) - strategy_count
    static_count = sum(item["label"] is not None for item in entries)
    dynamic_count = len(entries) - static_count
    unique_static_count = len(
        {item["label"] for item in entries if item["label"] is not None}
    )
    evaluation_count = sum(is_evaluation(item) for item in entries)
    implemented_count = sum(lean_mapping(item)[1] == "implemented" for item in entries)
    mechanism_counts = {
        name: sum(mechanism_class(item) == name for item in entries)
        for name in (
            "local_schema",
            "reflection",
            "transform",
            "strategy",
            "definition",
            "quantified",
            "legacy_custom",
        )
    }
    lines = [
        "# Litex-to-Lean Builtin Rule Inventory",
        "",
        "Generated from production Rust source by",
        "[`generate_builtin_inventory.py`](generate_builtin_inventory.py).",
        "Do not hand-edit the table; update the generator's mapping policy and regenerate.",
        "",
        "## Scope and counting contract",
        "",
        f"The inventory contains **{len(entries)} label-bearing builtin success sites**:",
        f"**{rule_count} builtin-rule sites** and **{strategy_count} builtin-strategy sites**.",
        f"The lower-level source contains {raw_constructor_count} direct success-constructor calls; expanding",
        "their forwarding helpers exposes the label-bearing sites below. The repository's",
        f"informal 'about 500 rules' estimate is therefore closest to the {unique_static_count}",
        f"distinct static labels, while {len(entries)} is the exhaustive source-site count used here.",
        "Forwarding helpers such as a constructor receiving `reason.to_string()` are",
        "collapsed into their outer label-bearing callers. This is why the count is a",
        "semantic call-site count rather than a raw constructor grep. A dynamic site",
        "appears once with its source expression even when it can render several labels",
        "at runtime.",
        "",
        "`Mechanism class` describes the executable proof shape independently of",
        "the diagnostic label. The classification is deliberately conservative:",
        "unaudited or mixed branches remain `legacy_custom`.",
        "",
        f"Of these sites, {static_count} have a static string label and {dynamic_count} use",
        f"a dynamic label expression. {evaluation_count} evaluation/computation-like sites",
        "are explicitly marked `not_this_round`. The classification is intentionally",
        "conservative and source-derived; it does not claim one Rust site equals one",
        "mathematical theorem schema.",
        "",
        "A Lean mapping is recorded only when the current backend actually emits and the",
        "Lean kernel checks that tactic or lemma. `none` means no checked mapping exists",
        "yet for that individual local rule schema, not that Lean lacks the mathematics.",
        f"The generic local-schema site currently represents {LOCAL_BUILTIN_RULE_COUNT} paired RuleIds;",
        "the implemented summary still counts source sites, not catalog entries.",
        "Closed numeric membership results may instead use the backend's generic,",
        "carrier-bearing `norm_num` reflection path. The closed-u64 `$prime` route is",
        "listed as implemented because it now carries explicit structured reflection",
        "evidence; other evaluation sites remain `not_this_round`.",
        "",
        "Regenerate or audit drift with:",
        "",
        "```text",
        "python3 src/compile_to_lean/generate_builtin_inventory.py --write",
        "python3 src/compile_to_lean/generate_builtin_inventory.py --check",
        "```",
        "",
        "## Summary",
        "",
        "| Metric | Count |",
        "| --- | ---: |",
        f"| Total label-bearing sites | {len(entries)} |",
        f"| Direct success-constructor calls | {raw_constructor_count} |",
        f"| Builtin rules | {rule_count} |",
        f"| Builtin strategies | {strategy_count} |",
        f"| Static labels | {static_count} |",
        f"| Distinct static labels | {unique_static_count} |",
        f"| Dynamic label expressions | {dynamic_count} |",
        f"| Evaluation/computation (`not_this_round`) | {evaluation_count} |",
        f"| Checked Lean mappings currently implemented | {implemented_count} |",
        f"| Forwarding sink functions discovered | {len(sinks)} |",
        *(
            f"| Mechanism: `{name}` | {count} |"
            for name, count in mechanism_counts.items()
        ),
        "",
        "## Rule sites",
        "",
        "| ID | Kind | Mechanism class | Label or dynamic expression | Source | Family | Checked Lean mapping | Status |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for index, entry in enumerate(entries, 1):
        label = entry["label"]
        rendered = label if label is not None else f"dynamic: {entry['expression']}"
        rendered = rendered.replace("|", "\\|").replace("`", "'")
        source = f"`{entry['path']}:{entry['line']}`"
        mapping, status = lean_mapping(entry)
        lines.append(
            f"| B{index:04d} | {entry['kind']} | `{mechanism_class(entry)}` | {rendered} | {source} | "
            f"{family(entry)} | {mapping} | `{status}` |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    sources = {path: path.read_text() for path in rust_files()}
    functions_by_path = {path: function_ranges(source) for path, source in sources.items()}
    sinks = discover_sinks(sources, functions_by_path)
    entries = inventory_entries(sources, functions_by_path, sinks)
    raw_constructor_count = sum(
        1
        for source in sources.values()
        for sink_name in INITIAL_SINKS
        for _ in find_calls(source, sink_name)
    )
    generated = markdown(entries, sinks, raw_constructor_count)

    if args.write:
        OUTPUT.write_text(generated)
        print(f"wrote {OUTPUT.relative_to(ROOT)} with {len(entries)} sites")
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text() != generated:
        print(f"{OUTPUT.relative_to(ROOT)} is stale; run with --write")
        return 1
    print(f"checked {OUTPUT.relative_to(ROOT)} with {len(entries)} sites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
