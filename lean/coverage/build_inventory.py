#!/usr/bin/env python3
"""Build the direct StmtResult-to-Lean source coverage inventory."""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import io
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[2]
COVERAGE_DIR = Path(__file__).resolve().parent
INVENTORY_PATH = COVERAGE_DIR / "inventory.json"
SUMMARY_PATH = COVERAGE_DIR / "summary.md"
TYPED_QUEUE_PATH = COVERAGE_DIR / "typed_builtin_queue.tsv"
UNCATALOGUED_QUEUE_PATH = COVERAGE_DIR / "uncatalogued_builtin_queue.tsv"
BUILTIN_ROUTE_CANDIDATES_PATH = COVERAGE_DIR / "builtin_to_lean_route_candidates.tsv"
MECHANISM_FAMILIES_PATH = COVERAGE_DIR / "uncatalogued_mechanism_families.md"
TRACER_GATE_EVIDENCE_PATH = COVERAGE_DIR / "tracer_gate_evidence.json"
GAP_REPORT_PATH = COVERAGE_DIR / "gaps.md"
LEAN_ADAPTER_SYMBOLS_PATH = COVERAGE_DIR / "lean_adapter_symbols.tsv"
DYNAMIC_LEAN_ADAPTER_SITES_PATH = COVERAGE_DIR / "dynamic_lean_adapter_sites.tsv"
LEAN_ADAPTER_CHECKS_PATH = COVERAGE_DIR / "LeanAdapterSymbols.lean"
LEAN_ADAPTER_GATE_EVIDENCE_PATH = COVERAGE_DIR / "lean_adapter_gate_evidence.json"
INTEGRATION_GATE_EVIDENCE_PATH = COVERAGE_DIR / "integration_gate_evidence.json"
INTEGRATION_FAILURE_FAMILIES_PATH = COVERAGE_DIR / "integration_failure_families.tsv"
INTEGRATION_TEST_INVENTORY_PATH = COVERAGE_DIR / "integration_test_inventory.tsv"
EXAMPLE_MATRIX_PATH = COVERAGE_DIR / "example_kernel_matrix.json"
CHECKED_EXAMPLE_GATE_PATH = COVERAGE_DIR / "checked_example_kernel_evidence.json"
EXAMPLE_TRUST_BOUNDARIES_PATH = COVERAGE_DIR / "example_trust_boundaries.tsv"
REQUIRED_TRACER_QUEUE_PATH = COVERAGE_DIR / "required_tracer_queue.tsv"

STATUS_KERNEL_CHECKED = "kernel_checked"
STATUS_MAPPED = "mapped_not_kernel_checked"
STATUS_COMPILER_GAP = "compiler_gap"
STATUS_EVIDENCE_GAP = "evidence_gap"
STATUS_ABI_DECISION = "abi_decision"
STATUS_UNREACHABLE = "unreachable"
STATUS_DEAD_OR_DUPLICATE = "dead_or_duplicate_candidate"

LEAN_SYMBOL = re.compile(r"Litex(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
DYNAMIC_LEAN_SYMBOL = re.compile(
    r"Litex(?:\.(?:[A-Za-z_][A-Za-z0-9_]*|\{[A-Za-z_][A-Za-z0-9_]*\}))+"
)
LEAN_NAMESPACE_ONLY = {
    "Litex.OrderBridge",
    "Litex.Rules",
    "Litex.SetRules",
}

OBJECT_ROLES = (
    "term",
    "binder",
    "target_set",
    "definition_value",
    "function_domain_or_codomain",
    "well_definedness",
)

STATEMENT_RESULT_PAIRS = (
    ("Stmt", "SuccessStmtResult"),
    ("UnsafeStmt", "SuccessUnsafeStmtResult"),
    ("DefinitionStmt", "SuccessDefinitionStmtResult"),
    ("ByStmt", "SuccessByStmtResult"),
    ("WitnessStmt", "SuccessWitnessStmtResult"),
    ("ProofBlockStmt", "SuccessProofBlockStmtResult"),
    ("CommandStmt", "SuccessCommandStmtResult"),
)

MECHANISM_MIGRATIONS = {
    "mathematical_leaf_law": (
        "Promote the producer to a typed certificate that fixes the exact target and required premises.",
        "Call one named proved Lean theorem adapter after certificate validation; keep one explicit route per stable ID.",
    ),
    "checked_computation_or_reflection": (
        "Retain the checked input, normalized output, and reflection witness instead of a display result.",
        "Use a fixed kernel-checked reflection theorem; never ask a target tactic to rediscover the computation.",
    ),
    "proof_composition_or_recursive_strategy": (
        "Retain ordered child Results and the composition constructor selected by the verifier.",
        "Compile children first and assemble their proofs with one structural Lean combinator.",
    ),
    "dispatcher_or_search_helper": (
        "Return the selected terminal certificate/child Result; retire a helper identity that proves no proposition.",
        "Do not create a theorem for search control flow; compile only the selected semantic certificate.",
    ),
    "duplicate_or_orientation_candidate": (
        "Compare exact targets, premise order, orientation, and retained evidence before merging schemas.",
        "Share a proved theorem only after validation, while preserving an explicit route for every stable rule ID.",
    ),
    "evidence_contract_gap": (
        "Extend the verifier Result with the missing target, binding, FactId, scope, or ordered child evidence.",
        "Keep fail-closed until the richer evidence can select one deterministic proof adapter.",
    ),
    "target_abi_decision": (
        "Freeze the exact native carrier/wrapper and required eliminators before changing the certificate.",
        "Block emission until the user-owned semantic decision has a proved Core/Rules contract.",
    ),
}

MECHANISM_ROUTE_KINDS = {
    "mathematical_leaf_law": "leaf_theorem_adapter",
    "checked_computation_or_reflection": "fixed_reflection_adapter",
    "proof_composition_or_recursive_strategy": "recursive_result_composition",
    "dispatcher_or_search_helper": "selected_semantic_child",
    "duplicate_or_orientation_candidate": "shared_adapter_candidate",
    "evidence_contract_gap": "blocked_evidence_contract",
    "target_abi_decision": "blocked_target_abi",
}


@dataclass(frozen=True)
class EnumSpec:
    axis: str
    enum_name: str
    path: str
    result_evidence: str
    lean_dependency: str


ENUM_SPECS = (
    EnumSpec(
        "object",
        "Obj",
        "src/object/object.rs",
        "source object identity plus occurrence-owned WD and representation evidence",
        "native Lean term/type and Litex semantic wrapper",
    ),
    EnumSpec(
        "object_atom",
        "AtomObj",
        "src/object/atom.rs",
        "SymbolId-backed atom identity and binder ownership",
        "compiler environment binding",
    ),
    EnumSpec("statement", "Stmt", "src/statement/statement.rs", "completed recursive StmtResult", "top-level declaration or local proof scope"),
    EnumSpec("statement", "UnsafeStmt", "src/statement/statement.rs", "explicit unsafe statement Result", "visible source trust boundary"),
    EnumSpec("statement", "DefinitionStmt", "src/statement/statement.rs", "definition Result with stored facts and scope effects", "Lean declaration and retained FactIds"),
    EnumSpec("statement", "ByStmt", "src/statement/statement.rs", "structured proof Result with owned child Results", "Lean proof scope and eliminator"),
    EnumSpec("statement", "WitnessStmt", "src/statement/statement.rs", "witness Result and projected facts", "Lean constructor or choice/elimination"),
    EnumSpec("statement", "ProofBlockStmt", "src/statement/statement.rs", "proof-block Result and local scope", "Lean theorem/example/local scope"),
    EnumSpec("statement", "CommandStmt", "src/statement/statement.rs", "command execution Result", "declaration-free compiler effect"),
    EnumSpec("statement_result", "SuccessStmtResult", "src/result/statement/success/outcome.rs", "canonical completed statement result", "result dispatcher"),
    EnumSpec("statement_result", "SuccessUnsafeStmtResult", "src/result/statement/success/unsafe_statements.rs", "unsafe statement result", "source-scoped axiom/trust adapter"),
    EnumSpec("statement_result", "SuccessDefinitionStmtResult", "src/result/statement/success/definition_outcome.rs", "definition result", "definition compiler"),
    EnumSpec("statement_result", "SuccessByStmtResult", "src/result/statement/success/explicit_verification.rs", "structured proof result", "structured proof compiler"),
    EnumSpec("statement_result", "SuccessWitnessStmtResult", "src/result/statement/success/witnesses.rs", "witness result", "witness compiler"),
    EnumSpec("statement_result", "SuccessProofBlockStmtResult", "src/result/statement/success/proof_blocks.rs", "proof block result", "proof-scope compiler"),
    EnumSpec("statement_result", "SuccessCommandStmtResult", "src/result/statement/success/evaluation.rs", "command result", "command compiler"),
    EnumSpec("fact", "Fact", "src/fact/fact.rs", "source proposition identity and WD proof", "Lean proposition rendering"),
    EnumSpec("atomic_fact", "AtomicFact", "src/fact/atomic/atomic_fact.rs", "atomic target plus proof evidence", "Lean atomic proposition and proof replay"),
    EnumSpec("fact_proof", "SuccessFactProofResult", "src/result/verification/success/proof_composition.rs", "verifier-selected recursive proof constructor", "deterministic Lean proof replay"),
    EnumSpec("inference", "InferRule", "src/inference/result/infer_rule.rs", "typed inference application with ordered premises and stored FactIds", "local/persistent inferred theorem publication"),
)


def rust_files() -> dict[str, list[str]]:
    files: dict[str, list[str]] = {}
    for path in sorted((ROOT / "src").rglob("*.rs")):
        relative = path.relative_to(ROOT).as_posix()
        files[relative] = path.read_text(encoding="utf-8").splitlines()
    return files


def inventory_source_fingerprint() -> str:
    paths = list((ROOT / "src").rglob("*.rs"))
    paths.extend((ROOT / "lean/examples").glob("*.lit"))
    paths.extend((ROOT / "lean/examples").glob("*.lean"))
    paths.extend((ROOT / "lean/Litex").rglob("*.lean"))
    paths.extend(
        path
        for path in (
            ROOT / "lean/examples/litex.config",
            ROOT / "lean/Litex.lean",
            ROOT / "lean/lakefile.lean",
            ROOT / "lean/lean-toolchain",
        )
        if path.exists()
    )
    digest = hashlib.sha256()
    for path in sorted(set(paths)):
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        digest.update(relative)
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def lean_dependency_fingerprint() -> str:
    paths = list((ROOT / "lean/Litex").rglob("*.lean"))
    paths.extend(
        path
        for path in (
            ROOT / "lean/Litex.lean",
            ROOT / "lean/lakefile.lean",
            ROOT / "lean/lean-toolchain",
        )
        if path.exists()
    )
    digest = hashlib.sha256()
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def rust_source_fingerprint() -> str:
    paths = list((ROOT / "src").rglob("*.rs"))
    paths.extend(
        path
        for path in (ROOT / "Cargo.toml", ROOT / "Cargo.lock")
        if path.exists()
    )
    digest = hashlib.sha256()
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def file_sha256(relative: str) -> str | None:
    path = ROOT / relative
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_dependency_forbidden_hits() -> list[str]:
    pattern = re.compile(
        r"^\s*(?:axiom|sorry|admit)\b|\bby\s+(?:sorry|admit)\b"
    )
    paths = list((ROOT / "lean/Litex").rglob("*.lean"))
    paths.append(ROOT / "lean/Litex.lean")
    hits: list[str] = []
    for path in sorted(set(paths)):
        if not path.exists():
            continue
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            if pattern.search(line):
                hits.append(
                    f"{path.relative_to(ROOT).as_posix()}:{line_number}:{line.strip()}"
                )
    return hits


def enum_variants(path: Path, enum_name: str) -> list[tuple[str, int]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    declaration = re.compile(rf"^pub enum {re.escape(enum_name)}(?:\s|\{{)")
    variant = re.compile(r"^\s{4}([A-Z][A-Za-z0-9_]*)\b")
    active = False
    depth = 0
    result: list[tuple[str, int]] = []
    for line_number, line in enumerate(lines, 1):
        if not active and declaration.search(line):
            active = True
        if not active:
            continue
        if depth == 1:
            match = variant.match(line)
            if match and not line.lstrip().startswith(("pub ", "impl ")):
                name = match.group(1)
                if not result or result[-1][0] != name:
                    result.append((name, line_number))
        depth += line.count("{") - line.count("}")
        if depth == 0 and "}" in line:
            break
    if not result:
        raise ValueError(f"no variants found for {enum_name} in {path}")
    return result


def token_index(files: dict[str, list[str]]) -> dict[str, list[str]]:
    index: dict[str, list[str]] = collections.defaultdict(list)
    token = re.compile(r"\b[A-Z][A-Za-z0-9_]*::[A-Z][A-Za-z0-9_]*\b")
    for path, lines in files.items():
        for line_number, line in enumerate(lines, 1):
            for value in set(token.findall(line)):
                index[value].append(f"{path}:{line_number}")
    return dict(index)


def compiler_lean_symbols(files: dict[str, list[str]]) -> dict[str, list[str]]:
    symbols: dict[str, list[str]] = collections.defaultdict(list)
    for path, lines in files.items():
        if not path.startswith("src/stmt_result_to_lean_compiler/"):
            continue
        for line_number, line in enumerate(lines, 1):
            for symbol in sorted(set(LEAN_SYMBOL.findall(line))):
                if symbol not in LEAN_NAMESPACE_ONLY:
                    symbols[symbol].append(f"{path}:{line_number}")
    return dict(sorted(symbols.items()))


def compiler_dynamic_lean_symbols(
    files: dict[str, list[str]],
) -> dict[str, list[str]]:
    symbols: dict[str, list[str]] = collections.defaultdict(list)
    for path, lines in files.items():
        if not path.startswith("src/stmt_result_to_lean_compiler/"):
            continue
        for line_number, line in enumerate(lines, 1):
            for symbol in sorted(set(DYNAMIC_LEAN_SYMBOL.findall(line))):
                if "{" in symbol:
                    symbols[symbol].append(f"{path}:{line_number}")
    return dict(sorted(symbols.items()))


def enclosing_rust_function_start(
    lines: list[str], line_number: int
) -> tuple[str, int]:
    declaration = re.compile(
        r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)"
    )
    for index in range(min(line_number - 1, len(lines) - 1), -1, -1):
        line = lines[index]
        match = declaration.match(line)
        if match:
            return match.group(1), index
    return "<module>", 0


def enclosing_rust_function(lines: list[str], line_number: int) -> str:
    return enclosing_rust_function_start(lines, line_number)[0]


def enclosing_rust_function_lines(lines: list[str], line_number: int) -> list[str]:
    _, function_start = enclosing_rust_function_start(lines, line_number)
    declaration = re.compile(
        r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+[A-Za-z_][A-Za-z0-9_]*"
    )
    function_end = len(lines)
    for index in range(function_start + 1, len(lines)):
        if declaration.match(lines[index]):
            function_end = index
            break
    return lines[function_start:function_end]


def function_certificate_symbols(lines: list[str], line_number: int) -> list[str]:
    pattern = re.compile(
        r"\b[A-Z][A-Za-z0-9_]*(?:Rule|RuleEvidence)::[A-Z][A-Za-z0-9_]*\b"
    )
    return sorted(
        {
            symbol
            for line in enclosing_rust_function_lines(lines, line_number)
            for symbol in pattern.findall(line)
        }
    )


def dynamic_route_counts(files: dict[str, list[str]]) -> dict[str, int]:
    counts = collections.Counter()
    for references in compiler_dynamic_lean_symbols(files).values():
        for reference in references:
            path, line_text = reference.rsplit(":", 1)
            route = (
                "direct_certificate_match"
                if function_certificate_symbols(files[path], int(line_text))
                else "caller_selected_helper"
            )
            counts[route] += 1
    return dict(sorted(counts.items()))


def function_lean_surfaces(
    files: dict[str, list[str]], reference: str
) -> tuple[set[str], set[str]]:
    path, line_text = reference.rsplit(":", 1)
    if path not in files or not line_text.isdigit():
        return set(), set()
    lines = enclosing_rust_function_lines(files[path], int(line_text))
    literals = {
        symbol
        for line in lines
        for symbol in LEAN_SYMBOL.findall(line)
        if symbol not in LEAN_NAMESPACE_ONLY
    }
    dynamic = {
        symbol
        for line in lines
        for symbol in DYNAMIC_LEAN_SYMBOL.findall(line)
        if "{" in symbol
    }
    return literals, dynamic


def builtin_route_resolution(
    item: dict[str, object], files: dict[str, list[str]]
) -> tuple[str, set[str], set[str]]:
    literals: set[str] = set()
    dynamic: set[str] = set()
    for reference in item["compiler_consumers"]:
        local_literals, local_dynamic = function_lean_surfaces(
            files, str(reference)
        )
        literals.update(local_literals)
        dynamic.update(local_dynamic)
    if item["status"] != STATUS_MAPPED:
        resolution = str(item["status"])
    elif literals or dynamic:
        resolution = "candidate_needs_result_tracer"
    else:
        resolution = "callee_trace_required"
    return resolution, literals, dynamic


def builtin_route_kind(item: dict[str, object]) -> str:
    if item["axis"] == "builtin_uncatalogued":
        return MECHANISM_ROUTE_KINDS[str(item["mechanism"])]
    if item["status"] == STATUS_ABI_DECISION:
        return "blocked_target_abi"
    if item["status"] == STATUS_EVIDENCE_GAP:
        return "blocked_evidence_contract"
    if item["status"] == STATUS_COMPILER_GAP:
        return "missing_typed_certificate_route"
    return "typed_certificate_route"


def selector_binding(
    path: str, lines: list[str], line_number: int, selector: str
) -> tuple[str, str]:
    _, function_start = enclosing_rust_function_start(lines, line_number)
    token = re.compile(rf"\b{re.escape(selector)}\b")
    for index in range(line_number - 2, function_start - 1, -1):
        line = lines[index]
        binding_side = line.split("=", 1)[0]
        if ("let " in binding_side and token.search(binding_side)) or re.search(
            rf"\bfor\s+{re.escape(selector)}\s+in\b", line
        ):
            return f"{path}:{index + 1}", line.strip()
    parameter = re.compile(rf"\b{re.escape(selector)}\s*:\s*[^:]")
    for index in range(line_number - 2, function_start - 1, -1):
        if parameter.search(lines[index]):
            return f"{path}:{index + 1}", lines[index].strip()
    return "<unresolved>", "<unresolved>"


def standalone_references(
    name: str, files: dict[str, list[str]], prefixes: tuple[str, ...]
) -> list[str]:
    pattern = re.compile(rf"\b{re.escape(name)}\b")
    result: list[str] = []
    for path, lines in files.items():
        if not path.startswith(prefixes):
            continue
        for line_number, line in enumerate(lines, 1):
            if pattern.search(line):
                result.append(f"{path}:{line_number}")
    return result


def split_references(
    references: Iterable[str], declaration_path: str
) -> tuple[list[str], list[str], list[str]]:
    producer: list[str] = []
    consumer: list[str] = []
    observer: list[str] = []
    for reference in references:
        path = reference.split(":", 1)[0]
        if path == declaration_path:
            continue
        if path.startswith("src/stmt_result_to_lean_compiler/"):
            consumer.append(reference)
        elif path.startswith(("src/output/", "src/graph/", "src/latex_renderer/")):
            observer.append(reference)
        else:
            producer.append(reference)
    return producer, consumer, observer


def result_enum_for_source(enum_name: str) -> str | None:
    return dict(STATEMENT_RESULT_PAIRS).get(enum_name)


def statement_result_parity() -> dict[str, int]:
    specs = {spec.enum_name: spec for spec in ENUM_SPECS}
    result: dict[str, int] = {}
    for source_name, result_name in STATEMENT_RESULT_PAIRS:
        source_spec = specs[source_name]
        result_spec = specs[result_name]
        source_variants = {
            name
            for name, _ in enum_variants(ROOT / source_spec.path, source_name)
        }
        result_variants = {
            name
            for name, _ in enum_variants(ROOT / result_spec.path, result_name)
        }
        if source_variants != result_variants:
            raise ValueError(
                f"statement/result mismatch for {source_name}/{result_name}: "
                f"source_only={sorted(source_variants - result_variants)}, "
                f"result_only={sorted(result_variants - source_variants)}"
            )
        result[f"{source_name}->{result_name}"] = len(source_variants)
    return result


def default_next_gate(axis: str, source_id: str, status: str) -> str:
    if axis == "tracer" and status == STATUS_UNREACHABLE:
        return f"decide whether to register {source_id} or move it outside the configured examples module"
    if status == STATUS_UNREACHABLE:
        return f"prove a real producer or delete/retire {source_id}"
    if status == STATUS_EVIDENCE_GAP:
        return f"inspect the exact producer Result and replace generic evidence for {source_id}"
    if status == STATUS_DEAD_OR_DUPLICATE:
        return f"prove there is no constructor, compare sibling schemas, then retire or restore {source_id}"
    if status == STATUS_COMPILER_GAP:
        return f"add one positive Result-driven tracer and direct compiler consumer for {source_id}"
    if status == STATUS_ABI_DECISION:
        return f"freeze the Lean representation contract before compiling {source_id}"
    if axis == "tracer":
        return "run strict Litex, drift, and real Lean gates"
    return f"attach a positive tracer and real Lean kernel gate for {source_id}"


def default_positive_tracer(
    axis: str, source_id: str, status: str, occurrence_role: str | None
) -> str:
    if status in (STATUS_UNREACHABLE, STATUS_DEAD_OR_DUPLICATE):
        return "not applicable until a production route is proved or the identity is retired"
    role = f" in its {occurrence_role} role" if occurrence_role else ""
    if axis.startswith("builtin_"):
        return f"required: smallest .lit source whose Result selects stable ID {source_id}"
    return f"required: smallest .lit source whose completed Result contains {source_id}{role}"


def default_negative_boundary(source_id: str, status: str) -> str:
    if status == STATUS_ABI_DECISION:
        return f"reject {source_id} emission until its target ABI and eliminators are frozen"
    if status == STATUS_EVIDENCE_GAP:
        return f"reject {source_id} when target, ordered children, FactIds, bindings, or scope evidence is absent"
    if status == STATUS_COMPILER_GAP:
        return f"return an explicit incomplete/error result for {source_id}; never accept partial Lean"
    if status in (STATUS_UNREACHABLE, STATUS_DEAD_OR_DUPLICATE):
        return f"do not count a synthetic {source_id} constructor as production coverage"
    return f"reject a forged {source_id} Result with mismatched target, evidence, order, or effects"


def explicit_source_limitations() -> dict[str, tuple[str, str, str]]:
    object_path = "src/stmt_result_to_lean_compiler/object_representation.rs"
    audit_path = (
        "src/stmt_result_to_lean_compiler/compiler/validation/"
        "direct_compilation_audit.rs"
    )
    fact_dispatch_path = (
        "src/stmt_result_to_lean_compiler/compiler/fact_proof_dispatch.rs"
    )

    def reference(path: str, needle: str) -> str:
        for line_number, line in enumerate(
            (ROOT / path).read_text(encoding="utf-8").splitlines(), 1
        ):
            if needle in line:
                return f"{path}:{line_number}"
        raise ValueError(f"missing source limitation marker {needle} in {path}")

    result = {
        "Obj::Quot": (
            STATUS_COMPILER_GAP,
            "object lowering explicitly rejects the builtin quot object",
            reference(object_path, "Obj::Quot(_)"),
        ),
        "Obj::IndexUnion": (
            STATUS_ABI_DECISION,
            "native indexed-union semantics are intentionally deferred",
            reference(object_path, "Obj::IndexUnion(_)"),
        ),
        "Obj::IndexIntersect": (
            STATUS_ABI_DECISION,
            "native indexed-intersection semantics are intentionally deferred",
            reference(object_path, "Obj::IndexIntersect(_)"),
        ),
        "SuccessFactProofResult::DefinitionReduction": (
            STATUS_COMPILER_GAP,
            "direct proof replay returns no proof for the legacy definition-reduction Result",
            reference(
                fact_dispatch_path,
                "SuccessFactProofResult::DefinitionReduction(_)",
            ),
        ),
        "SuccessFactProofResult::DiagnosticOnly": (
            STATUS_EVIDENCE_GAP,
            "a diagnostic-only successful Result retains no replayable proof evidence",
            reference(
                fact_dispatch_path,
                "SuccessFactProofResult::DiagnosticOnly(_)",
            ),
        ),
    }
    matrix_reference = reference(
        audit_path, "BuiltinRuleEvidence::MatrixExpressionMembership"
    )
    for variant in (
        "MatrixAdd",
        "MatrixListObj",
        "MatrixMul",
        "MatrixPow",
        "MatrixScalarMul",
        "MatrixSub",
    ):
        result[f"Obj::{variant}"] = (
            STATUS_ABI_DECISION,
            "native matrix expressions do not yet have a reviewed Lean target ABI",
            matrix_reference,
        )
    return result


def row(
    *,
    axis: str,
    source_id: str,
    source_path: str,
    source_symbol: str | None,
    declaration_line: int | None,
    producers: list[str],
    consumers: list[str],
    result_evidence: str,
    lean_dependency: str,
    status: str,
    observers: list[str] | None = None,
    occurrence_role: str | None = None,
    mechanism: str | None = None,
    mechanism_basis: str | None = None,
    positive_tracer: str | None = None,
    negative_boundary: str | None = None,
    limitation: str | None = None,
    limitation_reference: str | None = None,
    consumer_route: str | None = None,
) -> dict[str, object]:
    reachable = "source_reference" if producers else "not_proven"
    owner = "user" if status == STATUS_ABI_DECISION else "Codex"
    tracer_state = (
        "existing"
        if positive_tracer
        else "not_applicable_until_reachable"
        if status in (STATUS_UNREACHABLE, STATUS_DEAD_OR_DUPLICATE)
        else "required"
    )
    return {
        "axis": axis,
        "source_id": source_id,
        "source_path": source_path,
        "source_symbol": source_symbol,
        "declaration_line": declaration_line,
        "occurrence_role": occurrence_role,
        "producer_reference_count": len(producers),
        "producer_references": producers,
        "observer_reference_count": len(observers or []),
        "observer_references": observers or [],
        "reachable": reachable,
        "result_evidence": result_evidence,
        "lean_dependency": lean_dependency,
        "compiler_consumer_count": len(consumers),
        "compiler_consumers": consumers,
        "consumer_route": consumer_route
        or ("direct_source_reference" if consumers else None),
        "positive_tracer": positive_tracer
        or default_positive_tracer(axis, source_id, status, occurrence_role),
        "negative_boundary": negative_boundary
        or default_negative_boundary(source_id, status),
        "tracer_evidence_state": tracer_state,
        "status": status,
        "owner": owner,
        "next_gate": default_next_gate(axis, source_id, status),
        "mechanism": mechanism,
        "mechanism_basis": mechanism_basis,
        "limitation": limitation,
        "limitation_reference": limitation_reference,
    }


def ordinary_enum_rows(
    files: dict[str, list[str]], index: dict[str, list[str]]
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    limitations = explicit_source_limitations()
    for spec in ENUM_SPECS:
        path = ROOT / spec.path
        for variant, line_number in enum_variants(path, spec.enum_name):
            source_token = f"{spec.enum_name}::{variant}"
            references = list(index.get(source_token, []))
            result_enum = result_enum_for_source(spec.enum_name)
            if result_enum:
                references.extend(index.get(f"{result_enum}::{variant}", []))
            producers, consumers, observers = split_references(references, spec.path)
            limitation = limitations.get(source_token)
            status = (
                limitation[0]
                if limitation
                else STATUS_MAPPED
                if consumers
                else STATUS_COMPILER_GAP
                if producers
                else STATUS_UNREACHABLE
            )
            roles: tuple[str | None, ...] = (
                OBJECT_ROLES if spec.enum_name == "Obj" else (None,)
            )
            for occurrence_role in roles:
                rows.append(
                    row(
                        axis=spec.axis,
                        source_id=source_token,
                        source_path=spec.path,
                        source_symbol=source_token,
                        declaration_line=line_number,
                        producers=producers,
                        consumers=consumers,
                        observers=observers,
                        result_evidence=spec.result_evidence,
                        lean_dependency=spec.lean_dependency,
                        status=status,
                        occurrence_role=occurrence_role,
                        limitation=limitation[1] if limitation else None,
                        limitation_reference=limitation[2] if limitation else None,
                    )
                )
    return rows


def public_declaration_blocks(
    root: Path,
) -> list[tuple[str, str, int, str]]:
    declarations: list[tuple[str, str, int, str]] = []
    declaration = re.compile(r"^pub (?:struct|enum) ([A-Z][A-Za-z0-9_]*)\b")
    for path in sorted(root.rglob("*.rs")):
        relative = path.relative_to(ROOT).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        line_index = 0
        while line_index < len(lines):
            line = lines[line_index]
            match = declaration.match(line)
            if not match:
                line_index += 1
                continue
            name = match.group(1)
            start = line_index
            block = [line]
            depth = line.count("{") - line.count("}")
            while depth > 0 and line_index + 1 < len(lines):
                line_index += 1
                block.append(lines[line_index])
                depth += lines[line_index].count("{") - lines[line_index].count("}")
            declarations.append((name, relative, start + 1, "\n".join(block)))
            line_index += 1
    return declarations


def well_definedness_rows(files: dict[str, list[str]]) -> list[dict[str, object]]:
    root = ROOT / "src/result/well_definedness"
    declarations = [
        declaration
        for declaration in public_declaration_blocks(root)
        if "WellDefined" in declaration[0]
        or declaration[0].startswith("SuccessVerify")
        or declaration[0].endswith("WellDefinedResult")
    ]
    names = {name for name, _, _, _ in declarations}
    contained_types: dict[str, set[str]] = {}
    direct: dict[str, tuple[list[str], list[str], list[str]]] = {}
    for name, relative, _, block in declarations:
        contained_types[name] = {
            candidate
            for candidate in names
            if candidate != name and re.search(rf"\b{re.escape(candidate)}\b", block)
        }
        direct[name] = split_references(
            standalone_references(name, files, ("src/",)), relative
        )

    consumers_by_name = {name: list(direct[name][1]) for name in names}
    routes = {
        name: "direct_source_reference"
        for name, consumers in consumers_by_name.items()
        if consumers
    }
    queue = collections.deque(sorted(routes))
    while queue:
        parent = queue.popleft()
        for child in sorted(contained_types[parent]):
            if consumers_by_name[child]:
                continue
            consumers_by_name[child] = [
                f"{reference} via {parent}"
                for reference in consumers_by_name[parent]
            ]
            routes[child] = f"enclosing_wd_type:{parent}"
            queue.append(child)

    rows: list[dict[str, object]] = []
    for name, relative, line_number, _ in declarations:
        producers = direct[name][0]
        consumers = consumers_by_name[name]
        status = STATUS_MAPPED if consumers else (
            STATUS_COMPILER_GAP if producers else STATUS_UNREACHABLE
        )
        rows.append(
            row(
                axis="well_definedness_result",
                source_id=name,
                source_path=relative,
                source_symbol=name,
                declaration_line=line_number,
                producers=producers,
                consumers=consumers,
                observers=direct[name][2],
                result_evidence="WD object/fact IDs, child roles, target requirements, binder scopes, and proof ownership",
                lean_dependency="statement-local child-before-parent proof replay",
                status=status,
                consumer_route=routes.get(name),
            )
        )
    return rows


RULE_ID = re.compile(r'"([a-z0-9_]+(?:\.[a-z0-9_]+)+)"')
SELF_VARIANT = re.compile(r"Self::([A-Z][A-Za-z0-9_]*)")
IMPL_NAME = re.compile(r"impl\s+([A-Z][A-Za-z0-9_]*)")


def rule_identities(path: Path) -> list[tuple[str, str, int]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    current_impl: str | None = None
    current_variant: str | None = None
    identities: list[tuple[str, str, int]] = []
    for line_number, line in enumerate(lines, 1):
        impl_match = IMPL_NAME.search(line)
        if impl_match:
            current_impl = impl_match.group(1)
            current_variant = None
        variant_match = SELF_VARIANT.search(line)
        if variant_match:
            current_variant = variant_match.group(1)
        for identity in RULE_ID.findall(line):
            if not current_impl:
                continue
            source_variant = current_variant or current_impl
            identities.append((identity, f"{current_impl}::{source_variant}", line_number))
    return identities


def builtin_wrapper_by_payload_type() -> dict[str, str]:
    path = ROOT / "src/result/verification/builtin_evidence/evidence.rs"
    lines = path.read_text(encoding="utf-8").splitlines()
    variants = dict(enum_variants(path, "BuiltinRuleEvidence"))
    result: dict[str, str] = {}
    declaration = re.compile(r"^\s{4}([A-Z][A-Za-z0-9_]*)\(([A-Z][A-Za-z0-9_]*)\),")
    for line in lines:
        match = declaration.match(line)
        if match and match.group(1) in variants:
            result[match.group(2)] = f"BuiltinRuleEvidence::{match.group(1)}"
    return result


def explicit_typed_limitations() -> dict[str, tuple[str, str, str]]:
    """Return limitations stated by the compiler's exhaustive fail-closed audit."""
    relative = "src/stmt_result_to_lean_compiler/compiler/validation/direct_compilation_audit.rs"

    def reference(needle: str, source_path: str = relative) -> str:
        source_lines = (ROOT / source_path).read_text(encoding="utf-8").splitlines()
        for line_number, line in enumerate(source_lines, 1):
            if needle in line:
                return f"{source_path}:{line_number}"
        raise ValueError(f"missing direct compiler limitation marker: {needle}")

    return {
        "matrix.expression_membership": (
            STATUS_ABI_DECISION,
            "native matrix expressions do not yet have a reviewed Lean target ABI",
            reference("BuiltinRuleEvidence::MatrixExpressionMembership"),
        ),
        "nonzero.div": (
            STATUS_EVIDENCE_GAP,
            "Litex.Same lacks the reviewed numeric-observation elimination required by division nonzero replay",
            reference("builtin rule `nonzero.div`"),
        ),
        "nonzero.mul": (
            STATUS_EVIDENCE_GAP,
            "Litex.Same lacks the reviewed numeric-observation elimination required by multiplication nonzero replay",
            reference("builtin rule `nonzero.mul`"),
        ),
        "not_equal.from_strict_order": (
            STATUS_EVIDENCE_GAP,
            "strict-order inequality replay lacks a reviewed numeric-observation elimination",
            reference("BuiltinRuleEvidence::NotEqualFromStrictOrder"),
        ),
        "set.set_minus_infinite_of_infinite_finite": (
            STATUS_ABI_DECISION,
            "the Lean target ABI does not yet represent infinite-set facts",
            reference(
                "SetBuiltinRule::SetMinusInfiniteOfInfiniteFinite",
                "src/stmt_result_to_lean_compiler/compiler/fact_proof_replay/set_builtin_rules.rs",
            ),
        ),
    }


def source_rule_ids() -> set[str]:
    evidence_root = ROOT / "src/result/verification/builtin_evidence"
    return {
        identity
        for path in evidence_root.glob("*.rs")
        for identity in RULE_ID.findall(path.read_text(encoding="utf-8"))
    }


def mechanism_for_uncatalogued(
    variant: str, producer_references: list[str], sibling_names: set[str]
) -> tuple[str, str]:
    lower = variant.lower()
    joined_paths = " ".join(producer_references).lower()
    if (
        "builtin_strategies/" in joined_paths
        or any(
            word in lower
            for word in (
                "withbuiltinrules",
                "withbuiltinstrategy",
                "builtinonly",
                "restrictedknownbuiltin",
                "dispatch",
            )
        )
    ):
        return "dispatcher_or_search_helper", "producer is an explicit builtin strategy/dispatcher boundary"
    if (
        "verification/composite/" in joined_paths
        or "execution/proof_directives/" in joined_paths
        or any(
            word in lower
            for word in (
                "result",
                "success",
                "steps",
                "parts",
                "dependency",
                "execbuiltinthm",
            )
        )
    ):
        return "proof_composition_or_recursive_strategy", "identity names an intermediate Result/composition boundary"
    if "inner" in lower:
        return "dispatcher_or_search_helper", "identity names a dispatcher/search boundary rather than a leaf law"
    if (
        "verification/quantified/" in joined_paths
        or "verification/atomic/definition.rs" in joined_paths
        or any(word in lower for word in ("bydefinition", "verifyforall", "verifyexist", "definitiontransport"))
    ):
        return "evidence_contract_gap", "definition/quantifier replay needs richer structured evidence than one identity"
    if any(word in lower for word in ("native", "directevaluation", "prime", "coprime", "factorial", "numericcomparison")):
        return "checked_computation_or_reflection", "producer is evaluation/reflection-shaped"
    numbered = re.match(r"^(.*?)(\d\d)$", variant)
    if numbered and any(name.startswith(numbered.group(1)) and name != variant for name in sibling_names):
        return "duplicate_or_orientation_candidate", "numbered sibling identities require schema comparison before separate theorems"
    if any(word in lower for word in ("matrix", "tuple", "cart", "replacement")):
        return "target_abi_decision", "producer targets a constructor family with an explicit object/fact compiler gap"
    return "mathematical_leaf_law", "default leaf candidate pending exact target/premise review"


def builtin_rows(
    files: dict[str, list[str]], index: dict[str, list[str]]
) -> list[dict[str, object]]:
    evidence_root = ROOT / "src/result/verification/builtin_evidence"
    uncatalogued_path = evidence_root / "uncatalogued_rules.rs"
    uncatalogued_variants = {
        name for name, _ in enum_variants(uncatalogued_path, "UncataloguedBuiltinRule")
    }
    rows: list[dict[str, object]] = []
    seen_ids: set[str] = set()
    wrapper_by_type = builtin_wrapper_by_payload_type()
    typed_limitations = explicit_typed_limitations()
    for path in sorted(evidence_root.glob("*.rs")):
        is_uncatalogued_file = path == uncatalogued_path
        relative = path.relative_to(ROOT).as_posix()
        for identity, qualified_variant, line_number in rule_identities(path):
            if identity in seen_ids:
                raise ValueError(f"duplicate stable builtin rule ID: {identity}")
            seen_ids.add(identity)
            enum_name, _, variant = qualified_variant.partition("::")
            token = f"{enum_name}::{variant}"
            references = index.get(token, [])
            producers, consumers, observers = split_references(references, relative)
            if enum_name == variant and not producers:
                wrapper = wrapper_by_type.get(enum_name)
                if wrapper:
                    wrapper_producers, wrapper_consumers, wrapper_observers = split_references(
                        index.get(wrapper, []), relative
                    )
                    producers.extend(wrapper_producers)
                    consumers.extend(wrapper_consumers)
                    observers.extend(wrapper_observers)
            is_uncatalogued = is_uncatalogued_file or enum_name == "UncataloguedBuiltinRule"
            mechanism = None
            mechanism_basis = None
            if is_uncatalogued:
                mechanism, mechanism_basis = mechanism_for_uncatalogued(
                    variant, producers, uncatalogued_variants
                )
                status = (
                    STATUS_MAPPED
                    if consumers
                    else STATUS_ABI_DECISION
                    if producers and mechanism == "target_abi_decision"
                    else STATUS_EVIDENCE_GAP
                    if producers
                    else STATUS_UNREACHABLE
                    if variant == "TestFixture"
                    else STATUS_DEAD_OR_DUPLICATE
                )
                axis = "builtin_uncatalogued"
                result_evidence = "uncatalogued stable identity plus enclosing generic target/subgoal Result; exact semantic certificate still requires review"
            else:
                limitation = typed_limitations.get(identity)
                status = (
                    limitation[0]
                    if limitation
                    else STATUS_MAPPED
                    if consumers
                    else STATUS_COMPILER_GAP
                    if producers
                    else STATUS_UNREACHABLE
                )
                axis = "builtin_typed"
                result_evidence = "typed builtin certificate selected by the verifier with target and ordered child Results"
            limitation = typed_limitations.get(identity) if not is_uncatalogued else None
            rows.append(
                row(
                    axis=axis,
                    source_id=identity,
                    source_path=relative,
                    source_symbol=token,
                    declaration_line=line_number,
                    producers=producers,
                    consumers=consumers,
                    observers=observers,
                    result_evidence=result_evidence,
                    lean_dependency="validated certificate mapped to a named proved Lean adapter",
                    status=status,
                    mechanism=mechanism,
                    mechanism_basis=mechanism_basis,
                    limitation=limitation[1] if limitation else None,
                    limitation_reference=limitation[2] if limitation else None,
                )
            )
    expected_ids = source_rule_ids()
    if seen_ids != expected_ids:
        missing = sorted(expected_ids - seen_ids)
        extra = sorted(seen_ids - expected_ids)
        raise ValueError(f"builtin rule identity mismatch: missing={missing}, extra={extra}")
    return rows


def tracer_rows() -> list[dict[str, object]]:
    examples = ROOT / "lean/examples"
    config = (examples / "litex.config").read_text(encoding="utf-8")
    gate_evidence = json.loads(TRACER_GATE_EVIDENCE_PATH.read_text(encoding="utf-8"))
    gated_source = Path(str(gate_evidence["tracer"])).name
    rows: list[dict[str, object]] = []
    for source in sorted(examples.glob("*.lit")):
        paired = source.with_suffix(".lean")
        registered = f'"./{source.name}"' in config
        source_gate_is_current = (
            source.name == gated_source
            and hashlib.sha256(source.read_bytes()).hexdigest()
            == gate_evidence["source_sha256"]
            and gate_evidence.get("current_valid") is True
            and gate_evidence.get("lean_dependency_fingerprint_sha256")
            == lean_dependency_fingerprint()
            and gate_evidence.get("rust_source_fingerprint_sha256")
            == rust_source_fingerprint()
            and file_sha256(str(gate_evidence["verifier_binary"]["path"]))
            == gate_evidence["verifier_binary"]["sha256"]
            and file_sha256(str(gate_evidence["compiler"]["binary_path"]))
            == gate_evidence["compiler"]["binary_sha256"]
        )
        kernel_checked = (
            source_gate_is_current
            and gate_evidence["isolated_verifier"]["exit"] == 0
            and gate_evidence["isolated_verifier"]["top_level_ok"]
            and gate_evidence["compiler"]["exit"] == 0
            and gate_evidence["generated_kernel"]["exit"] == 0
            and gate_evidence["checked_in_lean"]["kernel_exit"] == 0
        )
        if kernel_checked:
            status = STATUS_KERNEL_CHECKED
        elif registered and paired.exists():
            status = STATUS_MAPPED
        elif registered:
            status = STATUS_COMPILER_GAP
        else:
            status = STATUS_UNREACHABLE
        rows.append(
            row(
                axis="tracer",
                source_id=source.name,
                source_path=source.relative_to(ROOT).as_posix(),
                source_symbol=source.name,
                declaration_line=1,
                producers=[source.relative_to(ROOT).as_posix()],
                consumers=[paired.relative_to(ROOT).as_posix()] if paired.exists() else [],
                result_evidence="authoritative verified Litex source and generated same-name Lean output",
                lean_dependency="complete generated module accepted by the real Lean kernel",
                status=status,
                positive_tracer=source.relative_to(ROOT).as_posix(),
                negative_boundary="nearest compiler regression must remain fail-closed",
            )
        )
        rows[-1]["registered"] = registered
        rows[-1]["paired_output_exists"] = paired.exists()
        rows[-1]["gate_evidence"] = (
            "lean/coverage/tracer_gate_evidence.json"
            if source_gate_is_current
            else None
        )
        rows[-1]["generated_output_matches_checked_in"] = (
            gate_evidence["generated_drift"]["matches_checked_in"]
            if source_gate_is_current
            else None
        )
        if not registered:
            rows[-1]["owner"] = "user"
    return rows


def build_inventory() -> dict[str, object]:
    source_fingerprint_before = inventory_source_fingerprint()
    files = rust_files()
    index = token_index(files)
    stmt_result_parity = statement_result_parity()
    lean_symbols = compiler_lean_symbols(files)
    dynamic_lean_symbols = compiler_dynamic_lean_symbols(files)
    dynamic_routes = dynamic_route_counts(files)
    rows = ordinary_enum_rows(files, index)
    rows.extend(well_definedness_rows(files))
    rows.extend(builtin_rows(files, index))
    rows.extend(tracer_rows())
    rows.sort(
        key=lambda item: (
            str(item["axis"]),
            str(item["source_id"]),
            str(item.get("occurrence_role") or ""),
        )
    )
    axes = collections.Counter(str(item["axis"]) for item in rows)
    statuses = collections.Counter(str(item["status"]) for item in rows)
    owners = collections.Counter(str(item["owner"]) for item in rows)
    tracer_states = collections.Counter(
        str(item["tracer_evidence_state"]) for item in rows
    )
    mechanisms = collections.Counter(
        str(item["mechanism"]) for item in rows if item.get("mechanism")
    )
    axis_statuses: dict[str, dict[str, int]] = {}
    for axis in axes:
        counts = collections.Counter(
            str(item["status"]) for item in rows if item["axis"] == axis
        )
        axis_statuses[axis] = dict(sorted(counts.items()))
    builtin_rows_only = [item for item in rows if str(item["axis"]).startswith("builtin_")]
    uncatalogued_rows = [
        item for item in builtin_rows_only if item["axis"] == "builtin_uncatalogued"
    ]
    builtin_route_resolutions = collections.Counter(
        builtin_route_resolution(item, files)[0] for item in builtin_rows_only
    )
    builtin_route_kinds = collections.Counter(
        builtin_route_kind(item) for item in builtin_rows_only
    )
    trust_rows = example_trust_boundary_rows()
    trust_classes = collections.Counter(row["classification"] for row in trust_rows)
    source_fingerprint_after = inventory_source_fingerprint()
    if source_fingerprint_before != source_fingerprint_after:
        raise RuntimeError(
            "inventory source changed while the snapshot was being generated"
        )
    return {
        "schema_version": 1,
        "source_root": ".",
        "source_fingerprint_sha256": source_fingerprint_after,
        "summary": {
            "row_count": len(rows),
            "axes": dict(sorted(axes.items())),
            "statuses": dict(sorted(statuses.items())),
            "owners": dict(sorted(owners.items())),
            "tracer_evidence_states": dict(sorted(tracer_states.items())),
            "axis_statuses": dict(sorted(axis_statuses.items())),
            "uncatalogued_mechanisms": dict(sorted(mechanisms.items())),
            "builtin": {
                "stable_rule_ids": len(builtin_rows_only),
                "typed_rule_ids": sum(
                    item["axis"] == "builtin_typed" for item in builtin_rows_only
                ),
                "uncatalogued_rule_ids": len(uncatalogued_rows),
                "uncatalogued_with_direct_producer": sum(
                    bool(item["producer_reference_count"])
                    for item in uncatalogued_rows
                ),
                "uncatalogued_without_direct_producer": sum(
                    not bool(item["producer_reference_count"])
                    for item in uncatalogued_rows
                ),
                "user_owned": sum(item["owner"] == "user" for item in builtin_rows_only),
                "codex_owned": sum(item["owner"] == "Codex" for item in builtin_rows_only),
            },
            "statement_result_parity": stmt_result_parity,
            "lean_literal_adapter_symbols": len(lean_symbols),
            "lean_dynamic_adapter_templates": len(dynamic_lean_symbols),
            "lean_dynamic_adapter_sites": sum(
                len(references) for references in dynamic_lean_symbols.values()
            ),
            "lean_dynamic_route_classes": dynamic_routes,
            "builtin_route_candidate_resolutions": dict(
                sorted(builtin_route_resolutions.items())
            ),
            "builtin_route_kinds": dict(sorted(builtin_route_kinds.items())),
            "example_trust_boundaries": {
                "registered": len(trust_rows),
                "trust_free": trust_classes["trust_free"],
                "source_declared": trust_classes["source_declared_trust_boundary"],
                "unexpected_generated_axiom": trust_classes[
                    "unexpected_generated_axiom"
                ],
            },
        },
        "rows": rows,
    }


def validate_inventory_contract(inventory: dict[str, object]) -> None:
    rows = list(inventory["rows"])
    allowed_statuses = {
        STATUS_KERNEL_CHECKED,
        STATUS_MAPPED,
        STATUS_COMPILER_GAP,
        STATUS_EVIDENCE_GAP,
        STATUS_ABI_DECISION,
        STATUS_UNREACHABLE,
        STATUS_DEAD_OR_DUPLICATE,
    }
    seen: set[tuple[str, str, str]] = set()
    for item in rows:
        axis = str(item["axis"])
        source_id = str(item["source_id"])
        role = str(item.get("occurrence_role") or "")
        key = (axis, source_id, role)
        if key in seen:
            raise ValueError(f"duplicate inventory row: {key}")
        seen.add(key)

        status = str(item["status"])
        if status not in allowed_statuses:
            raise ValueError(f"unknown inventory status for {source_id}: {status}")
        for field in (
            "result_evidence",
            "lean_dependency",
            "positive_tracer",
            "negative_boundary",
            "owner",
            "next_gate",
        ):
            if not item.get(field):
                raise ValueError(f"inventory row lacks {field}: {source_id}")
        tracer_state = str(item.get("tracer_evidence_state"))
        if tracer_state not in (
            "existing",
            "required",
            "not_applicable_until_reachable",
        ):
            raise ValueError(f"invalid tracer evidence state for {source_id}")
        producer_count = int(item["producer_reference_count"])
        consumer_count = int(item["compiler_consumer_count"])
        if status in (STATUS_MAPPED, STATUS_KERNEL_CHECKED) and not consumer_count:
            raise ValueError(f"mapped row has no compiler consumer: {source_id}")
        if status == STATUS_UNREACHABLE and producer_count and axis != "tracer":
            raise ValueError(f"unreachable row has a producer: {source_id}")
        if axis == "builtin_uncatalogued":
            mechanism = item.get("mechanism")
            if mechanism not in MECHANISM_MIGRATIONS:
                raise ValueError(f"uncatalogued builtin lacks mechanism: {source_id}")
            if producer_count and status in (
                STATUS_UNREACHABLE,
                STATUS_DEAD_OR_DUPLICATE,
            ):
                raise ValueError(
                    f"production uncatalogued builtin has non-production status: {source_id}"
                )
        elif item.get("mechanism") is not None:
            raise ValueError(f"non-uncatalogued row has a mechanism: {source_id}")
        if axis.startswith("builtin_"):
            expected_owner = "user" if status == STATUS_ABI_DECISION else "Codex"
            if item["owner"] != expected_owner:
                raise ValueError(
                    f"builtin owner/status mismatch for {source_id}: "
                    f"{item['owner']} != {expected_owner}"
                )
        if axis == "builtin_typed" and status == STATUS_MAPPED:
            operational_consumers = [
                reference
                for reference in item["compiler_consumers"]
                if "/validation/" not in str(reference)
            ]
            if not operational_consumers:
                raise ValueError(
                    f"typed builtin is mentioned only by compiler validation: {source_id}"
                )

    builtin_ids = {
        str(item["source_id"])
        for item in rows
        if str(item["axis"]).startswith("builtin_")
    }
    if builtin_ids != source_rule_ids():
        raise ValueError("validated inventory no longer reconciles source rule IDs")


def render_json(inventory: dict[str, object]) -> str:
    return json.dumps(inventory, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def render_summary(inventory: dict[str, object]) -> str:
    summary = inventory["summary"]
    assert isinstance(summary, dict)
    lines = [
        "# StmtResult-to-Lean Coverage Summary",
        "",
        "Generated deterministically from current source by `build_inventory.py`.",
        "A source/compiler reference is not a real Lean kernel acceptance result.",
        "",
        f"Total rows: **{summary['row_count']}**",
        "",
        f"Source fingerprint (SHA-256): `{inventory['source_fingerprint_sha256']}`",
        "",
        "## Rows by axis",
        "",
        "| Axis | Rows |",
        "| --- | ---: |",
    ]
    for name, count in summary["axes"].items():
        lines.append(f"| `{name}` | {count} |")
    lines.extend(["", "## Rows by status", "", "| Status | Rows |", "| --- | ---: |"]) 
    for name, count in summary["statuses"].items():
        lines.append(f"| `{name}` | {count} |")
    lines.extend(
        [
            "",
            "## Rows by owner",
            "",
            f"- Codex implementation/evidence rows: **{summary['owners'].get('Codex', 0)}**",
            f"- User semantic-decision rows: **{summary['owners'].get('user', 0)}**",
            "",
            "Repeated role rows are collapsed into the seven questions in the Day 1 user decision packet.",
        ]
    )
    lines.extend(
        [
            "",
            "## Tracer obligations",
            "",
            f"- Existing source tracers: **{summary['tracer_evidence_states'].get('existing', 0)}**",
            f"- Required per-route tracers: **{summary['tracer_evidence_states'].get('required', 0)}**",
            f"- Not applicable until reachability/dead-code resolution: **{summary['tracer_evidence_states'].get('not_applicable_until_reachable', 0)}**",
            "",
            "A `required` string is an explicit obligation, not a claim that the tracer already exists.",
        ]
    )
    status_names = sorted(summary["statuses"])
    lines.extend(
        [
            "",
            "## Status by axis",
            "",
            "| Axis | " + " | ".join(f"`{name}`" for name in status_names) + " |",
            "| --- | " + " | ".join("---:" for _ in status_names) + " |",
        ]
    )
    for axis, counts in summary["axis_statuses"].items():
        lines.append(
            f"| `{axis}` | "
            + " | ".join(str(counts.get(name, 0)) for name in status_names)
            + " |"
        )
    lines.extend(
        [
            "",
            "## Lean adapter surface",
            "",
            f"- Compiler-emitted literal `Litex.*` symbols: **{summary['lean_literal_adapter_symbols']}**",
            f"- Interpolated Lean symbol templates: **{summary['lean_dynamic_adapter_templates']}**",
            f"- Interpolated compiler call sites: **{summary['lean_dynamic_adapter_sites']}**",
            f"- Dynamic sites with a function-local certificate match: **{summary['lean_dynamic_route_classes'].get('direct_certificate_match', 0)}**",
            f"- Dynamic sites selected by an enclosing caller/helper route: **{summary['lean_dynamic_route_classes'].get('caller_selected_helper', 0)}**",
            f"- Builtin IDs with a function-local Lean candidate: **{summary['builtin_route_candidate_resolutions'].get('candidate_needs_result_tracer', 0)}**",
            f"- Mapped builtin IDs requiring callee tracing: **{summary['builtin_route_candidate_resolutions'].get('callee_trace_required', 0)}**",
            "",
            "See `lean_adapter_symbols.tsv` and `LeanAdapterSymbols.lean` for the",
            "literal declaration gate. See `dynamic_lean_adapter_sites.tsv` for",
            "templates that require Result-driven generated-module tracers.",
        ]
    )
    lines.extend(
        [
            "",
            "### Builtin implementation route kinds",
            "",
            "| Route kind | Stable IDs |",
            "| --- | ---: |",
        ]
    )
    for name, count in summary["builtin_route_kinds"].items():
        lines.append(f"| `{name}` | {count} |")
    builtin = summary["builtin"]
    lines.extend(
        [
            "",
            "## Builtin identity reconciliation",
            "",
            f"- Stable rule IDs in source: **{builtin['stable_rule_ids']}**",
            f"- Typed/catalogued IDs: **{builtin['typed_rule_ids']}**",
            f"- Uncatalogued IDs: **{builtin['uncatalogued_rule_ids']}**",
            f"- Uncatalogued IDs with a direct production reference: **{builtin['uncatalogued_with_direct_producer']}**",
            f"- Uncatalogued IDs without a direct production reference: **{builtin['uncatalogued_without_direct_producer']}**",
            f"- User-owned ABI decisions: **{builtin['user_owned']}**",
            f"- Codex-owned implementation/evidence rows: **{builtin['codex_owned']}**",
        ]
    )
    lines.extend(
        [
            "",
            "## Statement/result parity",
            "",
            "| Source/result pair | Matched variants |",
            "| --- | ---: |",
        ]
    )
    for pair, count in summary["statement_result_parity"].items():
        lines.append(f"| `{pair}` | {count} |")
    trust = summary["example_trust_boundaries"]
    lines.extend(
        [
            "",
            "## Checked example trust boundaries",
            "",
            f"- Registered pairs: **{trust['registered']}**",
            f"- Trust-free positive pairs: **{trust['trust_free']}**",
            f"- Explicit source-declared trust/axiom pairs: **{trust['source_declared']}**",
            f"- Checked Lean axioms without a source boundary: **{trust['unexpected_generated_axiom']}**",
            "",
            "See `example_trust_boundaries.tsv` for exact source and Lean line references.",
        ]
    )
    lines.extend(
        [
            "",
            "## Used and unused uncatalogued builtin mechanisms",
            "",
            "| Mechanism | Rows |",
            "| --- | ---: |",
        ]
    )
    for name, count in summary["uncatalogued_mechanisms"].items():
        lines.append(f"| `{name}` | {count} |")
    lines.extend(
        [
            "",
            "## Required interpretation",
            "",
            "- `mapped_not_kernel_checked` still needs an executable `.lit/.lean` tracer.",
            "- `evidence_gap` uncatalogued rows need exact Result/certificate review.",
            "- `unreachable` is an extractor finding, not a theorem about runtime reachability.",
            "- Object rows are role-specific by design.",
            "",
        ]
    )
    return "\n".join(lines)


def render_uncatalogued_queue(inventory: dict[str, object]) -> str:
    output = io.StringIO(newline="")
    fields = (
        "stable_rule_id",
        "rust_symbol",
        "mechanism",
        "mechanism_basis",
        "status",
        "owner",
        "producer_reference_count",
        "producer_references",
        "compiler_consumers",
        "next_gate",
    )
    writer = csv.DictWriter(output, fieldnames=fields, dialect="excel-tab", lineterminator="\n")
    writer.writeheader()
    for item in inventory["rows"]:
        if item["axis"] != "builtin_uncatalogued":
            continue
        writer.writerow(
            {
                "stable_rule_id": item["source_id"],
                "rust_symbol": item["source_symbol"],
                "mechanism": item["mechanism"],
                "mechanism_basis": item["mechanism_basis"],
                "status": item["status"],
                "owner": item["owner"],
                "producer_reference_count": item["producer_reference_count"],
                "producer_references": ";".join(item["producer_references"]),
                "compiler_consumers": ";".join(item["compiler_consumers"]),
                "next_gate": item["next_gate"],
            }
        )
    return output.getvalue()


def render_typed_queue(inventory: dict[str, object]) -> str:
    rows = [
        item for item in inventory["rows"] if item["axis"] == "builtin_typed"
    ]
    output = io.StringIO(newline="")
    writer = csv.writer(output, dialect="excel-tab", lineterminator="\n")
    writer.writerow(
        (
            "stable_rule_id",
            "rust_symbol",
            "status",
            "owner",
            "producer_reference_count",
            "producer_references",
            "compiler_consumer_count",
            "compiler_consumers",
            "limitation",
            "limitation_reference",
            "next_gate",
        )
    )
    for item in rows:
        writer.writerow(
            (
                item["source_id"],
                item["source_symbol"],
                item["status"],
                item["owner"],
                item["producer_reference_count"],
                ";".join(item["producer_references"]),
                item["compiler_consumer_count"],
                ";".join(item["compiler_consumers"]),
                item.get("limitation") or "",
                item.get("limitation_reference") or "",
                item["next_gate"],
            )
        )
    return output.getvalue()


def render_builtin_route_candidates(
    inventory: dict[str, object], files: dict[str, list[str]]
) -> str:
    rows = [
        item
        for item in inventory["rows"]
        if str(item["axis"]).startswith("builtin_")
    ]
    output = io.StringIO(newline="")
    writer = csv.writer(output, dialect="excel-tab", lineterminator="\n")
    writer.writerow(
        (
            "stable_rule_id",
            "axis",
            "status",
            "owner",
            "route_kind",
            "compiler_consumers",
            "local_literal_adapter_candidates",
            "local_dynamic_adapter_templates",
            "route_resolution",
            "interpretation_boundary",
        )
    )
    for item in rows:
        resolution, literals, dynamic = builtin_route_resolution(item, files)
        route_kind = builtin_route_kind(item)
        writer.writerow(
            (
                item["source_id"],
                item["axis"],
                item["status"],
                item["owner"],
                route_kind,
                ";".join(item["compiler_consumers"]),
                ";".join(sorted(literals)),
                ";".join(sorted(dynamic)),
                resolution,
                "Function-local co-occurrence is a candidate only; exact Result dispatch and generated Lean must prove the route.",
            )
        )
    return output.getvalue()


def render_mechanism_families(inventory: dict[str, object]) -> str:
    groups: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    for item in inventory["rows"]:
        if item["axis"] == "builtin_uncatalogued":
            groups[str(item["mechanism"])].append(item)
    if set(groups) != set(MECHANISM_MIGRATIONS):
        raise ValueError(
            "uncatalogued mechanism mismatch: "
            f"rows={sorted(groups)}, declared={sorted(MECHANISM_MIGRATIONS)}"
        )

    lines = [
        "# Uncatalogued Builtin Mechanism Families",
        "",
        "Generated deterministically from the current source inventory. The",
        "classification is a migration queue, not a proof that similarly named",
        "rules have interchangeable semantics.",
        "",
    ]
    for mechanism in MECHANISM_MIGRATIONS:
        rows = groups[mechanism]
        used = [item for item in rows if item["producer_reference_count"]]
        mapped = [item for item in rows if item["compiler_consumer_count"]]
        representative = sorted(
            used or rows,
            key=lambda item: (-int(item["producer_reference_count"]), str(item["source_id"])),
        )[0]
        result_migration, lean_migration = MECHANISM_MIGRATIONS[mechanism]
        producer = (
            representative["producer_references"][0]
            if representative["producer_references"]
            else "no direct production reference"
        )
        lines.extend(
            [
                f"## `{mechanism}`",
                "",
                f"- Rows: **{len(rows)}**; direct producers: **{len(used)}**; exact compiler consumers: **{len(mapped)}**.",
                f"- Representative: `{representative['source_id']}` (`{representative['source_symbol']}`).",
                f"- Representative producer: `{producer}`.",
                f"- Result migration: {result_migration}",
                f"- Lean migration: {lean_migration}",
                f"- Classification basis: {representative['mechanism_basis']}.",
                "",
            ]
        )
    lines.extend(
        [
            "## Review boundary",
            "",
            "The user reviews carrier semantics, theorem sharing, and whether the",
            "representative law matches the intended mathematics. Codex owns exact",
            "producer tracing, certificate migration, explicit dispatch, and gates.",
            "",
        ]
    )
    return "\n".join(lines)


def render_gap_report(inventory: dict[str, object]) -> str:
    complete = {STATUS_KERNEL_CHECKED, STATUS_MAPPED}
    rows = [
        item
        for item in inventory["rows"]
        if item["axis"] != "builtin_uncatalogued" and item["status"] not in complete
    ]
    grouped: dict[tuple[str, str], list[dict[str, object]]] = collections.defaultdict(list)
    for item in rows:
        grouped[(str(item["axis"]), str(item["source_id"]))].append(item)

    lines = [
        "# Direct Compiler Gap Report",
        "",
        "Generated from the source-bound inventory. Object occurrence roles are",
        "combined here; the JSON inventory keeps one row per role.",
        "",
        "The 422 uncatalogued builtin identities are intentionally kept in",
        "`uncatalogued_builtin_queue.tsv` and summarized by",
        "`uncatalogued_mechanism_families.md`.",
        "",
        "| Axis | Source identity | Status | Roles | Producers | Limitation / next gate |",
        "| --- | --- | --- | --- | ---: | --- |",
    ]
    for (axis, source_id), items in sorted(grouped.items()):
        roles = sorted(
            str(item["occurrence_role"])
            for item in items
            if item.get("occurrence_role")
        )
        producer_count = max(int(item["producer_reference_count"]) for item in items)
        detail = str(items[0].get("limitation") or items[0]["next_gate"])
        lines.append(
            f"| `{axis}` | `{source_id}` | `{items[0]['status']}` | "
            f"{', '.join(f'`{role}`' for role in roles) or '-'} | "
            f"{producer_count} | {detail} |"
        )
    lines.extend(
        [
            "",
            f"Unique non-uncatalogued gap identities: **{len(grouped)}**.",
            "",
        ]
    )
    return "\n".join(lines)


def render_lean_adapter_symbols(files: dict[str, list[str]]) -> str:
    output = io.StringIO(newline="")
    writer = csv.writer(output, dialect="excel-tab", lineterminator="\n")
    writer.writerow(("lean_symbol", "compiler_reference_count", "compiler_references"))
    for symbol, references in compiler_lean_symbols(files).items():
        writer.writerow((symbol, len(references), ";".join(references)))
    return output.getvalue()


def render_dynamic_lean_adapter_sites(files: dict[str, list[str]]) -> str:
    output = io.StringIO(newline="")
    writer = csv.writer(output, dialect="excel-tab", lineterminator="\n")
    writer.writerow(
        (
            "lean_symbol_template",
            "selector_fields",
            "compiler_reference",
            "enclosing_function",
            "selector_binding_reference",
            "selector_binding",
            "certificate_symbol_count",
            "certificate_symbols",
            "route_class",
            "owner",
            "required_gate",
        )
    )
    for symbol, references in compiler_dynamic_lean_symbols(files).items():
        selectors = ",".join(re.findall(r"\{([A-Za-z_][A-Za-z0-9_]*)\}", symbol))
        for reference in references:
            path, line_text = reference.rsplit(":", 1)
            selector_names = selectors.split(",")
            bindings = [
                selector_binding(path, files[path], int(line_text), selector)
                for selector in selector_names
            ]
            certificate_symbols = function_certificate_symbols(
                files[path], int(line_text)
            )
            writer.writerow(
                (
                    symbol,
                    selectors,
                    reference,
                    enclosing_rust_function(files[path], int(line_text)),
                    ";".join(binding[0] for binding in bindings),
                    ";".join(binding[1] for binding in bindings),
                    len(certificate_symbols),
                    ";".join(certificate_symbols),
                    "direct_certificate_match"
                    if certificate_symbols
                    else "caller_selected_helper",
                    "Codex",
                    "Result-driven generated .lean tracer plus real Lean kernel acceptance",
                )
            )
    return output.getvalue()


def render_lean_adapter_checks(files: dict[str, list[str]]) -> str:
    lines = [
        "-- Generated by lean/coverage/build_inventory.py. DO NOT EDIT.",
        "import Litex",
        "",
        "namespace LitexCoverage",
        "",
    ]
    for symbol in compiler_lean_symbols(files):
        lines.append(f"#check {symbol}")
    lines.extend(["", "end LitexCoverage", ""])
    return "\n".join(lines)


def validate_tracer_gate_evidence() -> None:
    evidence = json.loads(TRACER_GATE_EVIDENCE_PATH.read_text(encoding="utf-8"))

    def digest(relative: str) -> str:
        path = ROOT / relative
        if not path.is_file():
            raise ValueError(f"tracer gate evidence path is missing: {relative}")
        return hashlib.sha256(path.read_bytes()).hexdigest()

    dependency_fingerprint = evidence.get("lean_dependency_fingerprint_sha256")
    if dependency_fingerprint is None:
        raise ValueError("primary tracer evidence does not bind Lean dependencies")
    if dependency_fingerprint != lean_dependency_fingerprint():
        raise ValueError("Lean dependencies changed after primary tracer evidence")
    if evidence.get("current_valid") is not True:
        raise ValueError("primary tracer evidence is marked invalid")
    rust_fingerprint = evidence.get("rust_source_fingerprint_sha256")
    if rust_fingerprint is None:
        raise ValueError("primary tracer evidence does not bind Rust sources")
    if rust_fingerprint != rust_source_fingerprint():
        raise ValueError("Rust sources changed after primary tracer evidence")
    verifier_binary = evidence.get("verifier_binary")
    if not isinstance(verifier_binary, dict):
        raise ValueError("primary tracer evidence does not bind the verifier binary")
    if digest(str(verifier_binary["path"])) != verifier_binary["sha256"]:
        raise ValueError("verifier binary changed after primary tracer evidence")
    compiler_binary_path = str(evidence["compiler"]["binary_path"])
    if digest(compiler_binary_path) != evidence["compiler"]["binary_sha256"]:
        raise ValueError("compiler binary changed after primary tracer evidence")

    actual_source = digest(str(evidence["tracer"]))
    if actual_source != evidence["source_sha256"]:
        raise ValueError("primary tracer source changed after gate evidence was recorded")
    checked_in = evidence["checked_in_lean"]
    actual_checked = digest(str(checked_in["path"]))
    if actual_checked != checked_in["sha256"]:
        raise ValueError("primary tracer checked-in Lean changed after gate evidence was recorded")
    project_mode = evidence["project_mode_verifier"]
    actual_config = digest(str(project_mode["config_path"]))
    if actual_config != project_mode["config_sha256"]:
        raise ValueError("project-mode tracer config changed after gate evidence was recorded")
    if evidence["isolated_verifier"]["exit"] != 0 or not evidence["isolated_verifier"]["top_level_ok"]:
        raise ValueError("recorded isolated verifier gate is not successful")
    if evidence["compiler"]["exit"] != 0 or evidence["generated_kernel"]["exit"] != 0:
        raise ValueError("recorded compiler/generated-kernel gate is not successful")
    if checked_in["kernel_exit"] != 0:
        raise ValueError("recorded checked-in Lean kernel gate is not successful")

    generated_hash = str(evidence["compiler"]["generated_sha256"])
    hashes_match = generated_hash == str(checked_in["sha256"])
    if bool(evidence["generated_drift"]["matches_checked_in"]) != hashes_match:
        raise ValueError("recorded generated drift disagrees with the bound file hashes")
    if not evidence["forbidden_construct_scan"]["clean"]:
        raise ValueError("primary tracer contains a forbidden trust or retired-ABI construct")
    forbidden_pattern = re.compile(
        r"\b(?:sorry|admit|axiom)\b|LitexObject|Litex\.Object|Set\.univ"
    )
    for relative in evidence["forbidden_construct_scan"]["paths"]:
        candidate = ROOT / str(relative)
        if candidate.exists() and forbidden_pattern.search(
            candidate.read_text(encoding="utf-8")
        ):
            raise ValueError(f"forbidden Lean construct in primary tracer: {relative}")

    generated = ROOT / str(evidence["compiler"]["generated_path"])
    if generated.exists():
        actual_generated = hashlib.sha256(generated.read_bytes()).hexdigest()
        if actual_generated != generated_hash:
            raise ValueError("primary tracer generated Lean changed after gate evidence was recorded")


def validate_lean_adapter_gate_evidence(files: dict[str, list[str]]) -> None:
    evidence = json.loads(
        LEAN_ADAPTER_GATE_EVIDENCE_PATH.read_text(encoding="utf-8")
    )

    def digest(relative: str) -> str:
        return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()

    dependency_fingerprint = evidence.get("lean_dependency_fingerprint_sha256")
    if dependency_fingerprint is None:
        raise ValueError("Lean adapter evidence does not bind Lean dependencies")
    if dependency_fingerprint != lean_dependency_fingerprint():
        raise ValueError("Lean dependencies changed after adapter evidence")
    source_fingerprint = evidence.get("inventory_source_fingerprint_sha256")
    if source_fingerprint != inventory_source_fingerprint():
        raise ValueError("inventory source changed after adapter evidence")
    rust_fingerprint = evidence.get("rust_source_fingerprint_sha256")
    if rust_fingerprint != rust_source_fingerprint():
        raise ValueError("Rust sources changed after adapter evidence")
    if evidence.get("current_valid") is not True:
        raise ValueError("Lean adapter evidence is marked invalid")

    if evidence["exit"] != 0:
        raise ValueError("recorded Lean adapter symbol gate is not successful")
    symbol_count = len(compiler_lean_symbols(files))
    if symbol_count != evidence["literal_symbol_count"]:
        raise ValueError("Lean adapter symbol count changed after gate evidence was recorded")
    if digest(str(evidence["checks_path"])) != evidence["checks_sha256"]:
        raise ValueError("Lean adapter #check file changed after gate evidence was recorded")
    if digest(str(evidence["ledger_path"])) != evidence["ledger_sha256"]:
        raise ValueError("Lean adapter symbol ledger changed after gate evidence was recorded")


def validate_integration_gate_evidence() -> None:
    evidence = json.loads(
        INTEGRATION_GATE_EVIDENCE_PATH.read_text(encoding="utf-8")
    )

    recorded_rust_fingerprint = evidence.get("rust_source_fingerprint_sha256")
    if not isinstance(recorded_rust_fingerprint, str) or len(recorded_rust_fingerprint) != 64:
        raise ValueError("compiler integration evidence lacks a Rust fingerprint")
    binary = evidence.get("test_binary")
    if not isinstance(binary, dict):
        raise ValueError("compiler integration evidence does not bind a test binary")
    if file_sha256(str(binary["path"])) != binary["sha256"]:
        raise ValueError("compiler integration test binary changed after evidence")
    cargo_binding = evidence.get("cargo_binding")
    if not isinstance(cargo_binding, dict) or cargo_binding.get("exit") != 0:
        raise ValueError("compiler integration evidence lacks a Cargo binding")
    if (
        cargo_binding.get("source_fingerprint_before") != recorded_rust_fingerprint
        or cargo_binding.get("source_fingerprint_after")
        != recorded_rust_fingerprint
    ):
        raise ValueError("Rust sources changed while binding the integration binary")
    source = evidence.get("test_source")
    if not isinstance(source, dict):
        raise ValueError("compiler integration evidence does not bind its test source")
    if file_sha256(str(source["path"])) != source["sha256"]:
        raise ValueError("compiler integration test source changed after evidence")
    ledger = evidence.get("failure_ledger")
    if not isinstance(ledger, dict):
        raise ValueError("compiler integration evidence does not bind its failure ledger")
    if file_sha256(str(ledger["path"])) != ledger["sha256"]:
        raise ValueError("compiler integration failure ledger changed after evidence")

    run = evidence.get("run")
    if not isinstance(run, dict) or run.get("exit") != 101:
        raise ValueError("compiler integration evidence lacks the expected red baseline")
    if (
        run.get("total") != 76
        or run.get("ignored") != 0
        or run.get("passed", 0) + run.get("failed", 0) != run.get("total")
    ):
        raise ValueError("compiler integration evidence totals do not reconcile")
    if (
        run.get("source_fingerprint_before") != recorded_rust_fingerprint
        or run.get("source_fingerprint_after") != recorded_rust_fingerprint
        or run.get("binary_sha256_before") != binary["sha256"]
        or run.get("binary_sha256_after") != binary["sha256"]
    ):
        raise ValueError("compiler integration run was not one stable snapshot")

    with INTEGRATION_FAILURE_FAMILIES_PATH.open(
        encoding="utf-8", newline=""
    ) as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if len(rows) != run["failed"]:
        raise ValueError("compiler integration ledger does not cover every failure")
    failure_names = [str(name) for name in run.get("failure_names", [])]
    ledger_names = [row["test"] for row in rows]
    if sorted(failure_names) != sorted(ledger_names):
        raise ValueError("compiler integration failure names disagree with the ledger")
    classes = collections.Counter(row["current_class"] for row in rows)
    if dict(sorted(classes.items())) != dict(
        sorted(evidence.get("classification_counts", {}).items())
    ):
        raise ValueError("compiler integration classifications do not reconcile")
    if evidence.get("current_valid") is not True:
        raise ValueError("compiler integration evidence is marked invalid")
    if recorded_rust_fingerprint != rust_source_fingerprint():
        raise ValueError("Rust sources changed after compiler integration evidence")


def validate_example_matrix_evidence() -> None:
    report = json.loads(EXAMPLE_MATRIX_PATH.read_text(encoding="utf-8"))
    schema_version = report.get("schema_version")
    if schema_version not in (2, 3):
        raise ValueError("example matrix has an unsupported schema")
    rows = report.get("rows")
    totals = report.get("totals")
    if not isinstance(rows, list) or not isinstance(totals, dict):
        raise ValueError("example matrix lacks rows or totals")
    names = [str(row["example"]) for row in rows]
    if len(names) != len(set(names)) or totals.get("registered") != len(rows):
        raise ValueError("example matrix row identities do not reconcile")

    config = (ROOT / "lean/examples/litex.config").read_text(encoding="utf-8")
    current_names = sorted(
        source.name
        for source in (ROOT / "lean/examples").glob("*.lit")
        if f'"./{source.name}"' in config
    )
    if sorted(names) != current_names:
        raise ValueError("registered example set changed after the matrix")
    expected_totals: dict[str, int] = {
        "registered": len(rows),
        "compiler_pass": sum(row["compiler_exit"] == 0 for row in rows),
        "matches_checked_in": sum(bool(row["matches_checked_in"]) for row in rows),
    }
    for prefix in ("generated_kernel", "checked_in_kernel"):
        for classification in (
            "pass",
            "kernel_reject",
            "infrastructure_failure",
            "not_run",
        ):
            expected_totals[f"{prefix}_{classification}"] = sum(
                row[f"{prefix}_class"] == classification for row in rows
            )
    if schema_version >= 3:
        expected_totals["generated_forbidden_rows"] = sum(
            bool(row["generated_forbidden_hits"]) for row in rows
        )
        expected_totals["checked_in_forbidden_rows"] = sum(
            bool(row["checked_in_forbidden_hits"]) for row in rows
        )
    if totals != expected_totals:
        raise ValueError("example matrix totals do not reconcile with its rows")

    if report.get("snapshot_valid") is not True:
        raise ValueError("example matrix is not a stable Rust/compiler/Lean snapshot")
    if report.get("compiler_stable_during_run") is not True:
        raise ValueError("example matrix compiler changed during the run")
    if report.get("example_inputs_stable_during_run") is not True:
        raise ValueError("example matrix inputs changed during the run")
    if report.get("lean_dependency_stable_during_run") is not True:
        raise ValueError("example matrix Lean dependencies changed during the run")
    if report.get("rust_source_stable_during_build_and_matrix") is not True:
        raise ValueError("example matrix lacks a stable Rust source binding")
    if report.get("olean_precondition_errors_before") or report.get(
        "olean_precondition_errors_after"
    ):
        raise ValueError("example matrix has stale or missing Lean object evidence")
    if schema_version < 3:
        raise ValueError("example matrix predates forbidden-output auditing")
    if totals.get("generated_forbidden_rows") or totals.get(
        "checked_in_forbidden_rows"
    ):
        raise ValueError("example matrix contains forbidden generated output")
    if report.get("lean_dependency_fingerprint_after") != lean_dependency_fingerprint():
        raise ValueError("Lean dependencies changed after the example matrix")
    if report.get("rust_source_fingerprint_after_matrix") != rust_source_fingerprint():
        raise ValueError("Rust sources changed after the example matrix")
    compiler_path = str(report["compiler_path"])
    if file_sha256(compiler_path) != report.get("compiler_sha256"):
        raise ValueError("release compiler changed after the example matrix")
    for row in rows:
        source = ROOT / "lean/examples" / str(row["example"])
        checked = ROOT / str(row["checked_in_path"])
        if hashlib.sha256(source.read_bytes()).hexdigest() != row["source_sha256"]:
            raise ValueError(f"example source changed after matrix: {row['example']}")
        if hashlib.sha256(checked.read_bytes()).hexdigest() != row["checked_in_sha256"]:
            raise ValueError(f"checked Lean changed after matrix: {row['example']}")


def validate_checked_example_gate_evidence() -> None:
    report = json.loads(CHECKED_EXAMPLE_GATE_PATH.read_text(encoding="utf-8"))
    rows = report.get("rows")
    totals = report.get("totals")
    if report.get("schema_version") != 1 or not isinstance(rows, list) or not isinstance(totals, dict):
        raise ValueError("checked-example gate has an unsupported schema")
    names = [str(row["example"]) for row in rows]
    config = (ROOT / "lean/examples/litex.config").read_text(encoding="utf-8")
    current_names = sorted(
        source.name
        for source in (ROOT / "lean/examples").glob("*.lit")
        if f'"./{source.name}"' in config
    )
    if sorted(names) != current_names or len(names) != len(set(names)):
        raise ValueError("checked-example gate does not cover the registered set")
    expected = {
        "registered": len(rows),
        "pass": sum(row["kernel_class"] == "pass" for row in rows),
        "kernel_reject": sum(row["kernel_class"] == "kernel_reject" for row in rows),
        "infrastructure_failure": sum(row["kernel_class"] == "infrastructure_failure" for row in rows),
        "forbidden_rows": sum(bool(row["forbidden_hits"]) for row in rows),
    }
    if totals != expected:
        raise ValueError("checked-example gate totals do not reconcile")
    if report.get("current_valid") is not True:
        raise ValueError("checked-example gate snapshot is unstable")
    if report.get("lean_dependency_fingerprint_after") != lean_dependency_fingerprint():
        raise ValueError("Lean dependencies changed after checked-example gate")
    if report.get("olean_precondition_errors_before") or report.get("olean_precondition_errors_after"):
        raise ValueError("checked-example gate has stale or missing oleans")
    for row in rows:
        source = ROOT / "lean/examples" / str(row["example"])
        checked = ROOT / str(row["checked_in_path"])
        if hashlib.sha256(source.read_bytes()).hexdigest() != row["source_sha256"]:
            raise ValueError(f"checked-example source changed: {row['example']}")
        if hashlib.sha256(checked.read_bytes()).hexdigest() != row["checked_in_sha256"]:
            raise ValueError(f"checked Lean changed: {row['example']}")
    if totals.get("forbidden_rows"):
        raise ValueError("checked examples contain forbidden output")
    if totals.get("pass") != totals.get("registered"):
        raise ValueError("checked examples contain kernel rejections")


def evidence_gate_issues(files: dict[str, list[str]]) -> list[str]:
    gates = (
        ("primary tracer", validate_tracer_gate_evidence),
        ("Lean adapter", lambda: validate_lean_adapter_gate_evidence(files)),
        ("compiler integration", validate_integration_gate_evidence),
        ("checked examples", validate_checked_example_gate_evidence),
        ("example matrix", validate_example_matrix_evidence),
    )
    issues: list[str] = []
    for label, gate in gates:
        try:
            gate()
        except (KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
            issues.append(f"{label}: {error}")
    return issues


def integration_test_rows() -> list[dict[str, str]]:
    relative_source = "tests/integration/stmt_result_to_lean_compiler_tracers.rs"
    lines = (ROOT / relative_source).read_text(encoding="utf-8").splitlines()
    test_pattern = re.compile(r"^fn ([A-Za-z_][A-Za-z0-9_]*)\(\) \{")
    tests = [
        (match.group(1), line_number)
        for line_number, line in enumerate(lines, 1)
        if (match := test_pattern.match(line))
    ]
    with INTEGRATION_FAILURE_FAMILIES_PATH.open(
        encoding="utf-8", newline=""
    ) as stream:
        failures = {
            row["test"]: row for row in csv.DictReader(stream, delimiter="\t")
        }
    names = {name for name, _ in tests}
    unknown = sorted(set(failures) - names)
    if unknown:
        raise ValueError(
            "integration failure ledger names missing from source: " + unknown[0]
        )
    rows: list[dict[str, str]] = []
    for name, line_number in tests:
        failure = failures.get(name)
        rows.append(
            {
                "test": name,
                "source_reference": f"{relative_source}:{line_number}",
                "baseline_outcome": "failed" if failure else "passed",
                "current_class": (
                    failure["current_class"] if failure else "baseline_pass"
                ),
                "first_boundary": failure["first_boundary"] if failure else "",
                "kernel_probe": failure["kernel_probe"] if failure else "broad gate pass",
                "owner": failure["owner"] if failure else "Codex regression gate",
                "next_gate": (
                    failure["next_gate"]
                    if failure
                    else "retain as a passing regression during focused repairs"
                ),
            }
        )
    return rows


def render_integration_test_inventory() -> str:
    columns = (
        "test",
        "source_reference",
        "baseline_outcome",
        "current_class",
        "first_boundary",
        "kernel_probe",
        "owner",
        "next_gate",
    )
    output = io.StringIO()
    writer = csv.DictWriter(
        output, fieldnames=columns, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(integration_test_rows())
    return output.getvalue()


def example_trust_boundary_rows() -> list[dict[str, str]]:
    examples = ROOT / "lean/examples"
    config = (examples / "litex.config").read_text(encoding="utf-8")
    source_pattern = re.compile(r"^\s*(abstract_prop|axiom|trust)\b")
    lean_axiom_pattern = re.compile(r"^\s*axiom\b")
    rows: list[dict[str, str]] = []
    for source in sorted(examples.glob("*.lit")):
        if f'"./{source.name}"' not in config:
            continue
        checked = source.with_suffix(".lean")
        source_boundaries: list[tuple[str, int]] = []
        for line_number, line in enumerate(
            source.read_text(encoding="utf-8").splitlines(), 1
        ):
            if match := source_pattern.match(line):
                source_boundaries.append((match.group(1), line_number))
        checked_axioms = [
            line_number
            for line_number, line in enumerate(
                checked.read_text(encoding="utf-8").splitlines(), 1
            )
            if lean_axiom_pattern.match(line)
        ]
        if checked_axioms and not source_boundaries:
            classification = "unexpected_generated_axiom"
        elif source_boundaries:
            classification = "source_declared_trust_boundary"
        else:
            classification = "trust_free"
        kinds = collections.Counter(kind for kind, _ in source_boundaries)
        rows.append(
            {
                "example": source.name,
                "classification": classification,
                "strict_positive_eligible": str(not source_boundaries).lower(),
                "source_boundary_count": str(len(source_boundaries)),
                "source_boundary_kinds": ";".join(
                    f"{kind}:{count}" for kind, count in sorted(kinds.items())
                ),
                "source_references": ";".join(
                    f"{source.relative_to(ROOT).as_posix()}:{line_number}"
                    for _, line_number in source_boundaries
                ),
                "checked_axiom_count": str(len(checked_axioms)),
                "checked_axiom_references": ";".join(
                    f"{checked.relative_to(ROOT).as_posix()}:{line_number}"
                    for line_number in checked_axioms
                ),
            }
        )
    return rows


def render_example_trust_boundaries() -> str:
    columns = (
        "example",
        "classification",
        "strict_positive_eligible",
        "source_boundary_count",
        "source_boundary_kinds",
        "source_references",
        "checked_axiom_count",
        "checked_axiom_references",
    )
    output = io.StringIO()
    writer = csv.DictWriter(
        output, fieldnames=columns, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(example_trust_boundary_rows())
    return output.getvalue()


def render_required_tracer_queue(inventory: dict[str, object]) -> str:
    columns = (
        "priority_band",
        "axis",
        "source_id",
        "occurrence_role",
        "status",
        "owner",
        "positive_tracer_obligation",
        "negative_boundary",
        "next_gate",
    )
    output = io.StringIO()
    writer = csv.DictWriter(
        output, fieldnames=columns, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    priority_by_status = {
        STATUS_ABI_DECISION: "P0_blocked_user_decision",
        STATUS_COMPILER_GAP: "P1_genuine_compiler_gap",
        STATUS_EVIDENCE_GAP: "P2_result_evidence_gap",
        STATUS_MAPPED: "P3_kernelize_mapped_route",
    }
    required_rows = [
        row_item
        for row_item in inventory["rows"]
        if row_item["tracer_evidence_state"] == "required"
    ]
    required_rows.sort(
        key=lambda row_item: (
            priority_by_status[str(row_item["status"])],
            str(row_item["axis"]),
            str(row_item["source_id"]),
            str(row_item.get("occurrence_role") or ""),
        )
    )
    for row_item in required_rows:
        priority_band = priority_by_status[str(row_item["status"])]
        writer.writerow(
            {
                "priority_band": priority_band,
                "axis": row_item["axis"],
                "source_id": row_item["source_id"],
                "occurrence_role": row_item.get("occurrence_role") or "",
                "status": row_item["status"],
                "owner": row_item["owner"],
                "positive_tracer_obligation": row_item["positive_tracer"],
                "negative_boundary": row_item["negative_boundary"],
                "next_gate": row_item["next_gate"],
            }
        )
    return output.getvalue()


def checked_example_forbidden_hits() -> list[str]:
    pattern = re.compile(r"\b(?:sorry|admit|LitexObject)\b|Litex\.Object|Set\.univ")
    hits: list[str] = []
    for path in sorted((ROOT / "lean/examples").glob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            if pattern.search(line):
                hits.append(
                    f"{path.relative_to(ROOT).as_posix()}:{line_number}:{line.strip()}"
                )
    return hits


def generate() -> int:
    inventory = build_inventory()
    files = rust_files()
    INVENTORY_PATH.write_text(render_json(inventory), encoding="utf-8")
    SUMMARY_PATH.write_text(render_summary(inventory), encoding="utf-8")
    TYPED_QUEUE_PATH.write_text(render_typed_queue(inventory), encoding="utf-8")
    UNCATALOGUED_QUEUE_PATH.write_text(
        render_uncatalogued_queue(inventory), encoding="utf-8"
    )
    BUILTIN_ROUTE_CANDIDATES_PATH.write_text(
        render_builtin_route_candidates(inventory, files), encoding="utf-8"
    )
    MECHANISM_FAMILIES_PATH.write_text(
        render_mechanism_families(inventory), encoding="utf-8"
    )
    GAP_REPORT_PATH.write_text(render_gap_report(inventory), encoding="utf-8")
    LEAN_ADAPTER_SYMBOLS_PATH.write_text(
        render_lean_adapter_symbols(files), encoding="utf-8"
    )
    DYNAMIC_LEAN_ADAPTER_SITES_PATH.write_text(
        render_dynamic_lean_adapter_sites(files), encoding="utf-8"
    )
    LEAN_ADAPTER_CHECKS_PATH.write_text(
        render_lean_adapter_checks(files), encoding="utf-8"
    )
    INTEGRATION_TEST_INVENTORY_PATH.write_text(
        render_integration_test_inventory(), encoding="utf-8"
    )
    EXAMPLE_TRUST_BOUNDARIES_PATH.write_text(
        render_example_trust_boundaries(), encoding="utf-8"
    )
    REQUIRED_TRACER_QUEUE_PATH.write_text(
        render_required_tracer_queue(inventory), encoding="utf-8"
    )
    print(f"generated {inventory['summary']['row_count']} coverage rows")
    return 0


def check() -> int:
    inventory = build_inventory()
    validate_inventory_contract(inventory)
    files = rust_files()
    expected = {
        INVENTORY_PATH: render_json(inventory),
        SUMMARY_PATH: render_summary(inventory),
        TYPED_QUEUE_PATH: render_typed_queue(inventory),
        UNCATALOGUED_QUEUE_PATH: render_uncatalogued_queue(inventory),
        BUILTIN_ROUTE_CANDIDATES_PATH: render_builtin_route_candidates(
            inventory, files
        ),
        MECHANISM_FAMILIES_PATH: render_mechanism_families(inventory),
        GAP_REPORT_PATH: render_gap_report(inventory),
        LEAN_ADAPTER_SYMBOLS_PATH: render_lean_adapter_symbols(files),
        DYNAMIC_LEAN_ADAPTER_SITES_PATH: render_dynamic_lean_adapter_sites(files),
        LEAN_ADAPTER_CHECKS_PATH: render_lean_adapter_checks(files),
        INTEGRATION_TEST_INVENTORY_PATH: render_integration_test_inventory(),
        EXAMPLE_TRUST_BOUNDARIES_PATH: render_example_trust_boundaries(),
        REQUIRED_TRACER_QUEUE_PATH: render_required_tracer_queue(inventory),
    }
    drift = []
    for path, content in expected.items():
        if not path.exists() or path.read_text(encoding="utf-8") != content:
            drift.append(path.relative_to(ROOT).as_posix())
    if drift:
        print("coverage inventory drift: " + ", ".join(drift), file=sys.stderr)
        return 1
    forbidden_hits = lean_dependency_forbidden_hits()
    if forbidden_hits:
        print(
            "coverage gate evidence invalid: Lean dependency contains proof hole: "
            + forbidden_hits[0],
            file=sys.stderr,
        )
        return 1
    example_forbidden_hits = checked_example_forbidden_hits()
    if example_forbidden_hits:
        print(
            "coverage gate evidence invalid: checked example contains forbidden output: "
            + example_forbidden_hits[0],
            file=sys.stderr,
        )
        return 1
    unexpected_axioms = [
        row
        for row in example_trust_boundary_rows()
        if row["classification"] == "unexpected_generated_axiom"
    ]
    if unexpected_axioms:
        print(
            "coverage gate evidence invalid: checked Lean has an axiom without a source trust boundary: "
            + unexpected_axioms[0]["example"],
            file=sys.stderr,
        )
        return 1
    evidence_issues = evidence_gate_issues(files)
    if evidence_issues:
        for issue in evidence_issues:
            print(f"coverage gate evidence invalid: {issue}", file=sys.stderr)
        return 1
    print(
        f"checked {inventory['summary']['row_count']} coverage rows: no drift; "
        "primary tracer and Lean adapter evidence are hash-bound"
    )
    return 0


def audit() -> int:
    result = check()
    if result:
        return result
    summary = build_inventory()["summary"]
    builtin = summary["builtin"]
    print(
        "audit summary: "
        f"builtin={builtin['stable_rule_ids']} "
        f"typed={builtin['typed_rule_ids']} "
        f"uncatalogued={builtin['uncatalogued_rule_ids']} "
        f"stmt_result_pairs={sum(summary['statement_result_parity'].values())} "
        f"lean_literal_symbols={summary['lean_literal_adapter_symbols']} "
        f"lean_dynamic_templates={summary['lean_dynamic_adapter_templates']} "
        f"lean_dynamic_sites={summary['lean_dynamic_adapter_sites']} "
        f"builtin_local_candidates={summary['builtin_route_candidate_resolutions'].get('candidate_needs_result_tracer', 0)} "
        f"builtin_callee_trace={summary['builtin_route_candidate_resolutions'].get('callee_trace_required', 0)}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "check", "audit"))
    args = parser.parse_args()
    if args.command == "generate":
        return generate()
    if args.command == "check":
        return check()
    return audit()


if __name__ == "__main__":
    raise SystemExit(main())
