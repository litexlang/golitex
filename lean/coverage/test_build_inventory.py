#!/usr/bin/env python3
"""Focused tests for the source coverage inventory generator."""

from __future__ import annotations

import importlib.util
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).resolve().parent / "build_inventory.py"
SPEC = importlib.util.spec_from_file_location("build_inventory", MODULE_PATH)
assert SPEC and SPEC.loader
BUILD_INVENTORY = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BUILD_INVENTORY
SPEC.loader.exec_module(BUILD_INVENTORY)

MATRIX_MODULE_PATH = Path(__file__).resolve().parent / "kernel_check_examples.py"
MATRIX_SPEC = importlib.util.spec_from_file_location(
    "kernel_check_examples", MATRIX_MODULE_PATH
)
assert MATRIX_SPEC and MATRIX_SPEC.loader
KERNEL_MATRIX = importlib.util.module_from_spec(MATRIX_SPEC)
sys.modules[MATRIX_SPEC.name] = KERNEL_MATRIX
MATRIX_SPEC.loader.exec_module(KERNEL_MATRIX)


class CoverageInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.inventory = BUILD_INVENTORY.build_inventory()

    def test_enum_variants_follow_only_the_selected_enum_body(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sample.rs"
            path.write_text(
                "pub enum First {\n"
                "    Alpha(Alpha),\n"
                "    Beta {\n"
                "        value: usize,\n"
                "    },\n"
                "}\n"
                "pub enum Second {\n"
                "    Gamma,\n"
                "}\n",
                encoding="utf-8",
            )
            self.assertEqual(
                BUILD_INVENTORY.enum_variants(path, "First"),
                [("Alpha", 2), ("Beta", 3)],
            )

    def test_uncatalogued_composition_is_not_called_a_leaf_law(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "ComplexEqualityResultWithSteps", [], set()
        )
        self.assertEqual(mechanism, "proof_composition_or_recursive_strategy")

    def test_theorem_application_execution_is_composition(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "ExecBuiltinThmStmtImpl",
            ["src/execution/proof_directives/theorem_application.rs:850"],
            set(),
        )
        self.assertEqual(mechanism, "proof_composition_or_recursive_strategy")

    def test_plain_set_law_is_not_an_automatic_abi_decision(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "VerifyInFactByKnownDirectSuperset",
            ["src/verification/builtin_rules/in_fact_builtin/set_membership.rs:10"],
            set(),
        )
        self.assertEqual(mechanism, "mathematical_leaf_law")

    def test_builtin_strategy_is_a_dispatcher(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "VerifySetMembershipWithBuiltinStrategy",
            ["src/verification/builtin_strategies/set_membership.rs:10"],
            set(),
        )
        self.assertEqual(mechanism, "dispatcher_or_search_helper")

    def test_untyped_cart_constructor_is_an_abi_decision(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "VerifyInFactInGeneralCartByDefiningFacts", [], set()
        )
        self.assertEqual(mechanism, "target_abi_decision")

    def test_reachable_cart_identity_is_user_owned_abi_work(self) -> None:
        inventory = self.inventory
        rows = {row["source_id"]: row for row in inventory["rows"]}
        cart = rows[
            "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_general_cart_by_defining_facts"
        ]
        self.assertEqual(cart["status"], "abi_decision")
        self.assertEqual(cart["owner"], "user")

    def test_numbered_siblings_are_duplicate_candidates(self) -> None:
        mechanism, _ = BUILD_INVENTORY.mechanism_for_uncatalogued(
            "TryLessAlgebra01", [], {"TryLessAlgebra01", "TryLessAlgebra02"}
        )
        self.assertEqual(mechanism, "duplicate_or_orientation_candidate")

    def test_inventory_has_every_required_axis(self) -> None:
        inventory = self.inventory
        axes = set(inventory["summary"]["axes"])
        self.assertTrue(
            {
                "object",
                "statement",
                "statement_result",
                "fact",
                "atomic_fact",
                "fact_proof",
                "inference",
                "well_definedness_result",
                "builtin_typed",
                "builtin_uncatalogued",
                "tracer",
            }.issubset(axes)
        )

    def test_inventory_contract_is_fail_closed(self) -> None:
        BUILD_INVENTORY.validate_inventory_contract(self.inventory)
        duplicated = {
            **self.inventory,
            "rows": [*self.inventory["rows"], self.inventory["rows"][0]],
        }
        with self.assertRaisesRegex(ValueError, "duplicate inventory row"):
            BUILD_INVENTORY.validate_inventory_contract(duplicated)

    def test_builtin_inventory_reconciles_every_source_rule_id(self) -> None:
        inventory = self.inventory
        inventory_ids = {
            row["source_id"]
            for row in inventory["rows"]
            if row["axis"].startswith("builtin_")
        }
        self.assertEqual(inventory_ids, BUILD_INVENTORY.source_rule_ids())

    def test_stable_builtin_rule_ids_are_globally_unique(self) -> None:
        evidence_root = BUILD_INVENTORY.ROOT / "src/result/verification/builtin_evidence"
        identities = [
            identity
            for path in evidence_root.glob("*.rs")
            for identity, _, _ in BUILD_INVENTORY.rule_identities(path)
        ]
        self.assertEqual(len(identities), len(set(identities)))

    def test_typed_review_queue_has_one_row_per_typed_rule(self) -> None:
        rendered = BUILD_INVENTORY.render_typed_queue(self.inventory)
        self.assertEqual(len(rendered.splitlines()), 200)
        self.assertIn("set.subset_transitivity", rendered)
        self.assertIn("matrix.expression_membership", rendered)
        self.assertIn("status\towner\t", rendered.splitlines()[0])

    def test_builtin_ownership_reconciles_total_ids(self) -> None:
        builtin = self.inventory["summary"]["builtin"]
        self.assertEqual(
            builtin["user_owned"] + builtin["codex_owned"],
            builtin["stable_rule_ids"],
        )

    def test_explicit_typed_limitations_are_not_reported_mapped(self) -> None:
        inventory = self.inventory
        rows = {row["source_id"]: row for row in inventory["rows"]}
        for identity, (status, _, _) in BUILD_INVENTORY.explicit_typed_limitations().items():
            self.assertEqual(rows[identity]["status"], status)
            self.assertIsNotNone(rows[identity]["limitation_reference"])

    def test_mapped_typed_rules_have_non_validation_consumers(self) -> None:
        for row in self.inventory["rows"]:
            if row["axis"] != "builtin_typed" or row["status"] != "mapped_not_kernel_checked":
                continue
            self.assertTrue(
                any("/validation/" not in ref for ref in row["compiler_consumers"]),
                row["source_id"],
            )

    def test_nested_wd_steps_inherit_the_enclosing_result_consumer(self) -> None:
        inventory = self.inventory
        rows = {row["source_id"]: row for row in inventory["rows"]}
        steps = rows["SuccessVerifyObjWellDefinedStepsResult"]
        self.assertEqual(steps["status"], "mapped_not_kernel_checked")
        self.assertTrue(str(steps["consumer_route"]).startswith("enclosing_wd_type:"))

    def test_mechanism_report_accounts_for_all_declared_families(self) -> None:
        report = BUILD_INVENTORY.render_mechanism_families(
            self.inventory
        )
        for mechanism in BUILD_INVENTORY.MECHANISM_MIGRATIONS:
            self.assertIn(f"## `{mechanism}`", report)

    def test_orphaned_production_identity_is_a_dead_or_duplicate_candidate(self) -> None:
        inventory = self.inventory
        rows = {row["source_id"]: row for row in inventory["rows"]}
        orphan = rows[
            "builtin.verify.verify_builtin_rules.abs_order_builtin.try_verify_abs_upper_bound"
        ]
        self.assertEqual(orphan["status"], "dead_or_duplicate_candidate")

    def test_builtin_test_fixture_remains_unreachable_not_production_debt(self) -> None:
        inventory = self.inventory
        rows = {row["source_id"]: row for row in inventory["rows"]}
        self.assertEqual(rows["builtin.test.fixture"]["status"], "unreachable")

    def test_primary_tracer_gate_evidence_is_bound_to_current_files(self) -> None:
        evidence = json.loads(
            (MODULE_PATH.parent / "tracer_gate_evidence.json").read_text(
                encoding="utf-8"
            )
        )
        if not evidence["current_valid"]:
            with self.assertRaisesRegex(ValueError, "does not bind Lean dependencies"):
                BUILD_INVENTORY.validate_tracer_gate_evidence()
            tracer = next(
                row
                for row in self.inventory["rows"]
                if row["axis"] == "tracer"
                and row["source_id"] == "54_ComplexAlgebraicCalculation.lit"
            )
            self.assertEqual(tracer["status"], "mapped_not_kernel_checked")
            self.assertIsNone(tracer["gate_evidence"])
            return

        BUILD_INVENTORY.validate_tracer_gate_evidence()

        def digest(relative: str) -> str:
            return hashlib.sha256((BUILD_INVENTORY.ROOT / relative).read_bytes()).hexdigest()

        self.assertEqual(digest(evidence["tracer"]), evidence["source_sha256"])
        self.assertEqual(
            digest(evidence["checked_in_lean"]["path"]),
            evidence["checked_in_lean"]["sha256"],
        )
        generated = BUILD_INVENTORY.ROOT / evidence["compiler"]["generated_path"]
        if generated.exists():
            self.assertEqual(
                hashlib.sha256(generated.read_bytes()).hexdigest(),
                evidence["compiler"]["generated_sha256"],
            )
        self.assertEqual(
            evidence["generated_drift"]["matches_checked_in"],
            evidence["compiler"]["generated_sha256"]
            == evidence["checked_in_lean"]["sha256"],
        )
        self.assertTrue(evidence["forbidden_construct_scan"]["clean"])
        tracer_rows = {
            row["source_id"]: row
            for row in self.inventory["rows"]
            if row["axis"] == "tracer"
        }
        tracer = tracer_rows["54_ComplexAlgebraicCalculation.lit"]
        self.assertEqual(tracer["status"], "kernel_checked")
        self.assertFalse(tracer["generated_output_matches_checked_in"])

    def test_inventory_has_a_content_bound_source_fingerprint(self) -> None:
        inventory = self.inventory
        fingerprint = inventory["source_fingerprint_sha256"]
        self.assertEqual(len(fingerprint), 64)
        self.assertEqual(fingerprint, BUILD_INVENTORY.inventory_source_fingerprint())

    def test_every_statement_leaf_has_a_same_named_success_result(self) -> None:
        parity = BUILD_INVENTORY.statement_result_parity()
        self.assertEqual(sum(parity.values()), 63)
        self.assertEqual(len(parity), 7)

    def test_explicitly_rejected_object_variants_are_not_reported_mapped(self) -> None:
        rows = [
            row
            for row in self.inventory["rows"]
            if row["axis"] == "object" and row["occurrence_role"] == "term"
        ]
        by_id = {row["source_id"]: row for row in rows}
        self.assertEqual(by_id["Obj::Quot"]["status"], "compiler_gap")
        self.assertEqual(by_id["Obj::IndexUnion"]["status"], "abi_decision")
        self.assertEqual(by_id["Obj::MatrixAdd"]["owner"], "user")

    def test_no_proof_result_branches_are_not_reported_mapped(self) -> None:
        rows = {row["source_id"]: row for row in self.inventory["rows"]}
        self.assertEqual(
            rows["SuccessFactProofResult::DefinitionReduction"]["status"],
            "compiler_gap",
        )
        self.assertEqual(
            rows["SuccessFactProofResult::DiagnosticOnly"]["status"],
            "evidence_gap",
        )

    def test_output_serializer_reference_is_not_a_producer(self) -> None:
        rows = {row["source_id"]: row for row in self.inventory["rows"]}
        transitivity = rows["set.subset_transitivity"]
        self.assertEqual(transitivity["producer_reference_count"], 1)
        self.assertGreater(transitivity["observer_reference_count"], 0)

    def test_short_gap_report_contains_real_gaps_not_mapped_rows(self) -> None:
        report = BUILD_INVENTORY.render_gap_report(self.inventory)
        self.assertIn("`set.subset_transitivity`", report)
        self.assertIn("`Obj::Quot`", report)
        self.assertIn("`SuccessFactProofResult::DefinitionReduction`", report)
        self.assertNotIn("`Fact::AtomicFact`", report)

    def test_unregistered_tracers_are_user_configuration_decisions(self) -> None:
        tracers = [
            row for row in self.inventory["rows"] if row["axis"] == "tracer"
        ]
        for tracer in tracers:
            if tracer["registered"]:
                continue
            self.assertEqual(tracer["owner"], "user")
            self.assertIn("register", tracer["next_gate"])

    def test_lean_adapter_gate_covers_compiler_literal_symbols(self) -> None:
        files = BUILD_INVENTORY.rust_files()
        symbols = BUILD_INVENTORY.compiler_lean_symbols(files)
        checks = BUILD_INVENTORY.render_lean_adapter_checks(files)
        self.assertGreater(len(symbols), 200)
        self.assertIn("Litex.SetRules.subsetTransitive", symbols)
        self.assertIn("#check Litex.SetRules.subsetTransitive", checks)
        self.assertNotIn("#check Litex.SetRules\n", checks)
        evidence = json.loads(
            (MODULE_PATH.parent / "lean_adapter_gate_evidence.json").read_text(
                encoding="utf-8"
            )
        )
        if evidence["current_valid"]:
            BUILD_INVENTORY.validate_lean_adapter_gate_evidence(files)
        else:
            with self.assertRaisesRegex(ValueError, "does not bind Lean dependencies"):
                BUILD_INVENTORY.validate_lean_adapter_gate_evidence(files)

    def test_dynamic_lean_adapter_sites_require_result_tracers(self) -> None:
        files = BUILD_INVENTORY.rust_files()
        symbols = BUILD_INVENTORY.compiler_dynamic_lean_symbols(files)
        self.assertIn("Litex.Rules.{theorem}", symbols)
        self.assertIn("Litex.SetRules.{theorem}", symbols)
        self.assertIn("Litex.OrderBridge.{theorem}", symbols)
        self.assertIn("Litex.{predicate}.congr", symbols)
        self.assertGreater(sum(map(len, symbols.values())), 30)
        rendered = BUILD_INVENTORY.render_dynamic_lean_adapter_sites(files)
        self.assertIn("Result-driven generated .lean tracer", rendered)
        self.assertEqual(len(rendered.splitlines()), 47)
        self.assertIn("\tenclosing_function\tselector_binding_reference\t", rendered.splitlines()[0])
        self.assertIn("\trender_closed_numeric_comparison_fact\t", rendered)
        self.assertNotIn("<unresolved>", rendered)
        self.assertIn("\tdirect_certificate_match\tCodex\t", rendered)
        self.assertIn("\tcaller_selected_helper\tCodex\t", rendered)
        route_counts = self.inventory["summary"]["lean_dynamic_route_classes"]
        self.assertEqual(sum(route_counts.values()), 46)

    def test_builtin_route_candidate_queue_has_every_stable_id(self) -> None:
        files = BUILD_INVENTORY.rust_files()
        rendered = BUILD_INVENTORY.render_builtin_route_candidates(
            self.inventory, files
        )
        self.assertEqual(len(rendered.splitlines()), 622)
        self.assertIn("set.subset_transitivity", rendered)
        self.assertIn("candidate_needs_result_tracer", rendered)
        self.assertIn("callee_trace_required", rendered)
        self.assertIn(
            "Function-local co-occurrence is a candidate only", rendered
        )
        resolutions = self.inventory["summary"][
            "builtin_route_candidate_resolutions"
        ]
        self.assertEqual(sum(resolutions.values()), 621)
        self.assertGreater(resolutions["candidate_needs_result_tracer"], 0)
        self.assertGreater(resolutions["callee_trace_required"], 0)

    def test_kernel_matrix_separates_missing_olean_from_kernel_rejection(self) -> None:
        self.assertEqual(KERNEL_MATRIX.kernel_class(0, ""), "pass")
        self.assertEqual(KERNEL_MATRIX.kernel_class(None, ""), "not_run")
        self.assertEqual(
            KERNEL_MATRIX.kernel_class(
                1, "error: object file 'Litex/Core.olean' does not exist"
            ),
            "infrastructure_failure",
        )
        self.assertEqual(
            KERNEL_MATRIX.kernel_class(1, "error: application type mismatch"),
            "kernel_reject",
        )

    def test_kernel_matrix_covers_every_registered_example(self) -> None:
        self.assertEqual(len(KERNEL_MATRIX.registered_sources()), 69)
        self.assertEqual(
            KERNEL_MATRIX.lean_dependency_fingerprint(),
            BUILD_INVENTORY.lean_dependency_fingerprint(),
        )
        self.assertEqual(BUILD_INVENTORY.lean_dependency_forbidden_hits(), [])

    def test_integration_failure_family_ledger_reconciles_current_baseline(self) -> None:
        path = Path(__file__).resolve().parent / "integration_failure_families.tsv"
        lines = path.read_text(encoding="utf-8").splitlines()
        self.assertEqual(len(lines), 22)
        rows = [line.split("\t") for line in lines[1:]]
        self.assertEqual(len({row[0] for row in rows}), 21)
        classes = {name: sum(row[1] == name for row in rows) for name in {
            "kernel_checked_expectation_drift",
            "kernel_checked_checked_in_drift",
            "compiler_gap",
        }}
        self.assertEqual(
            classes,
            {
                "kernel_checked_expectation_drift": 13,
                "kernel_checked_checked_in_drift": 2,
                "compiler_gap": 6,
            },
        )
        integration_source = (
            BUILD_INVENTORY.ROOT
            / "tests/integration/stmt_result_to_lean_compiler_tracers.rs"
        ).read_text(encoding="utf-8")
        for row in rows:
            self.assertIn(f"fn {row[0]}()", integration_source)


if __name__ == "__main__":
    unittest.main()
