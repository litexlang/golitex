use litex::prelude::*;
use litex::stmt_result_to_lean_compiler::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source,
    StmtResultToLeanCompilationPhase, StmtResultToLeanCompilationStatus,
};

fn compile_on_verifier_stack(source: &'static str, label: &'static str) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("compiler-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || compile_litex_source_to_lean_source(source, label))
        .expect("spawn compiler verifier thread")
        .join()
        .expect("compiler verifier thread panicked")
}

fn compile_direct_result_only_on_verifier_stack(
    source: &'static str,
    label: &'static str,
) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("direct-result-compiler-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || compile_litex_source_to_lean_source(source, label))
        .expect("spawn direct Result compiler verifier thread")
        .join()
        .expect("direct Result compiler verifier thread panicked")
}

fn capture_statement_results_json_on_verifier_stack(
    source: &'static str,
    label: &'static str,
) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("stmt-result-json-v2-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let mut runtime = Runtime::default();
            runtime.start_isolated_source(label);
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .map_err(|error| format!("{error:?}"))?;
            let mut results = Vec::new();
            for mut block in blocks {
                let statement = runtime
                    .parse_statement(&mut block)
                    .map_err(|error| format!("{error:?}"))?;
                let result = runtime
                    .execute_statement(&statement)
                    .map_err(|error| format!("{error:?}"))?;
                results.push(result);
            }
            drop(runtime);
            let rendered_results = results
                .iter()
                .map(litex::output::render_statement_result_json)
                .collect::<Vec<_>>();
            Ok(format!("[\n{}\n]", rendered_results.join(",\n")))
        })
        .expect("spawn statement-result JSON verifier thread")
        .join()
        .expect("statement-result JSON verifier thread panicked")
}

#[test]
fn named_real_less_to_less_equal_emits_only_its_source_declaration() {
    let generated = compile_on_verifier_stack(
        "thm order_bridge:\n    ? forall a, b R:\n        a < b\n        =>:\n            a <= b\n",
        "native_real_order.lit",
    )
    .expect("compile the source theorem");

    assert!(generated.contains("theorem order_bridge :"), "{generated}");
    assert_eq!(generated.matches("theorem order_bridge").count(), 1);
    assert!(!generated.contains("namespace Native"), "{generated}");
    assert!(
        !generated.contains("private theorem __native_certificate"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted() {
    const SOURCE: &str = include_str!("../../showcases/Litex_to_Lean_Mathlib_Pipeline/main.lit");
    const CHECKED_IN: &str =
        include_str!("../../showcases/Litex_to_Lean_Mathlib_Pipeline/Generated.lean");

    let generated =
        compile_on_verifier_stack(SOURCE, "main.lit").expect("compile the pipeline showcase");

    assert_eq!(generated, CHECKED_IN);
    assert!(generated.contains("theorem sum_first_odds :"));
    assert!(!generated.contains("theorem odd_sum_integer :"));
    assert!(!generated.contains("theorem square_integer :"));
    assert!(!generated.contains("theorem sum_first_ten_odds :"));
    assert!(!generated.contains("private theorem __native_certificate"));
    assert!(!generated.contains("namespace Native"));
    assert!(!generated.contains("namespace MathlibConsumer"));
    assert!(!generated.contains("Finset.Icc"));
    assert!(!SOURCE.contains("thm odd_sum_single"));
    assert!(!SOURCE.contains("thm odd_sum_step"));
    assert!(!SOURCE.contains("thm odd_square_step"));
    assert!(!SOURCE.contains("by thm"));
    assert_eq!(SOURCE.matches("\nforall n Z:").count(), 2);
    assert_eq!(SOURCE.matches("\nthm ").count(), 1);
    assert!(SOURCE.contains("n^2 + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2"));
    assert!(!SOURCE.contains("sum_first_ten_odds"));
    assert!(!SOURCE.contains("sum(1, 10, kth_odd)"));
    assert!(generated.contains("unfold Litex.fnApplyCarrier kth_odd"));
    assert!(!generated.contains("unfold Litex.fnApplyOwn kth_odd"));
    assert!(!generated.contains("theorem odd_sum_step"));
    assert!(!generated.contains("theorem odd_square_step"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn litex_to_mathlib_pipeline_property_companion_verifies_without_trust() {
    const SOURCE: &str = include_str!("fixtures/stmt_result_to_lean_compiler/property_flow.lit");

    let results = capture_statement_results_json_on_verifier_stack(SOURCE, "property_flow.lit")
        .expect("verify the property-centered companion source");

    assert!(results.contains("DefPropStmt"), "{results}");
    assert!(results.contains("is_square_of"), "{results}");
    assert!(results.contains("square_of_is_nonnegative"), "{results}");
    assert!(
        results.contains("sum_first_odds_is_square_of_n"),
        "{results}"
    );
    assert!(results.contains("sum_first_odds_nonnegative"), "{results}");
    assert!(!SOURCE.contains("trust"));
    assert!(!SOURCE.contains("abstract_prop"));
}

#[test]
fn real_sequence_definitions_stable_tracer_generated_lean_has_not_drifted() {
    const SOURCE: &str = include_str!("../../lean/examples/64_RealSequenceCompleteness.lit");
    const CHECKED_IN: &str = include_str!("../../lean/examples/64_RealSequenceCompleteness.lean");

    let generated = compile_on_verifier_stack(SOURCE, "64_RealSequenceCompleteness.lit")
        .expect("compile the stable real-sequence definition tracer");

    assert_eq!(generated, CHECKED_IN);
    assert!(generated.contains("def is_convergent_sequence"));
    assert!(generated.contains("def is_cauchy_sequence"));
    assert!(!generated.contains("theorem cauchy_sequence_converges"));
    assert!(!SOURCE.contains("real_cauchy_sequence_converges"));
    assert!(!SOURCE.contains("axiom"));
    assert!(!SOURCE.contains("trust"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
    assert!(!generated.contains("admit"));
}

#[test]
fn named_real_same_equality_emits_only_its_source_declaration() {
    let generated = compile_on_verifier_stack(
        "thm real_reflexivity:\n    ? forall a R:\n        a = a\n    a = a\n",
        "native_real_equality_boundary.lit",
    )
    .expect("compile the canonical heterogeneous-equality theorem");

    assert!(
        generated.contains("theorem real_reflexivity :"),
        "{generated}"
    );
    assert!(!generated.contains("namespace Native"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn known_forall_multi_conclusion_fact_id_provenance_compiles_both_exact_projections() {
    const SOURCE: &str = include_str!("../../lean/examples/57_KnownForallFactIdProvenance.lit");
    let generated = compile_on_verifier_stack(SOURCE, "57_KnownForallFactIdProvenance.lit")
        .expect("compile two conclusions from one exact known-forall source FactId");

    assert!(generated.contains("theorem paired_source :"), "{generated}");
    assert!(
        generated.contains(
            "paired_source (2 : ℝ) ((Litex.In.congr (Litex.Same.symm (Litex.Same.realComplex ((2 : ℝ)))) Litex.R).mp (Litex.Rules.complexRealInR (2 : ℝ)))"
        ),
        "{generated}"
    );
    assert!(
        generated.contains("theorem __fact2 : Litex.In (2 : ℝ) Litex.R"),
        "{generated}"
    );
    assert!(
        generated.contains("(paired_source (2 : ℝ) (__fact2)).2"),
        "the second application must directly reuse the exact-carrier FactId proof produced while compiling the first conclusion:\n{generated}"
    );
    assert!(generated.matches("paired_source (2 : ℝ)").count() >= 2);
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn nonempty_set_witness_compiles_its_local_result_and_membership_evidence() {
    let generated = compile_direct_result_only_on_verifier_stack(
        "witness $is_nonempty_set({1, 2}) from 1\n",
        "nonempty_set_witness_result.lit",
    )
    .expect("compile a nonempty-set witness from recursive Results");
    assert!(generated.contains("Litex.Set.Nonempty"), "{generated}");
    assert!(generated.contains("Litex.Set.coproduct"), "{generated}");
    assert!(generated.contains("__nonempty_witness"), "{generated}");
    assert!(generated.contains("Litex.Same.sumLeft"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn predicate_backed_witness_compiles_all_retained_fact_ids() {
    let generated = compile_on_verifier_stack(
        "prop has_copy(a R):\n    exist x R st {x = a}\nwitness $has_copy(2) from 2:\n    2 = 2\n",
        "predicate_backed_witness_result.lit",
    )
    .expect("compile a concrete-predicate witness from recursive Results");
    assert!(generated.contains("def has_copy"), "{generated}");
    assert!(generated.contains("unfold has_copy"), "{generated}");
    assert_eq!(
        generated.matches("theorem __fact").count(),
        3,
        "{generated}"
    );
    assert!(
        generated.contains("Litex.In (2 : ℝ) Litex.R"),
        "{generated}"
    );
    assert!(
        generated.contains("∃ (x : (Litex.R).Carrier), ∃ (__type_x : Litex.In x Litex.R)"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn stored_forall_projections_replay_prior_conclusion_fact_ids() {
    let generated = compile_on_verifier_stack(
        "forall a C, f fn(x R) R:\n    a = 1\n    =>:\n        1 $in R\n        a $in R\n        f(a) = f(a)\n",
        "forall_projection_probe.lit",
    )
    .expect("compile independently stored forall projections");
    assert_eq!(
        generated.matches("theorem __fact").count(),
        3,
        "{generated}"
    );
    assert!(
        generated.contains("Litex.Rules.complexRealInR"),
        "{generated}"
    );
    assert!(generated.contains("Litex.In.congr"), "{generated}");
    assert!(generated.contains("Litex.fnApply"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn anonymous_function_set_membership_compiles_its_pointwise_result_directly() {
    let generated = compile_on_verifier_stack(
        "fn(x R) R {x} $in fn(x R) R\n",
        "anonymous_function_set_membership_result.lit",
    )
    .expect("compile function-set membership from its recursive pointwise Result");
    assert!(generated.contains("Litex.fnSet"), "{generated}");
    assert!(generated.contains("Litex.In.own"), "{generated}");
    assert!(generated.contains("Litex.Fn"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn combined_conjunction_and_chain_procedures_compile_each_recursive_component_result() {
    let generated = compile_on_verifier_stack(
        "1 = 1 and 2 = 2\n1 = 1 = 1\n",
        "combined_fact_procedures_result.lit",
    )
    .expect("compile conjunction and chain component Results without compatibility lowering");
    assert!(generated.contains("⟨Litex.Same.refl (1 : ℂ), Litex.Same.refl (2 : ℂ)⟩"));
    assert!(generated.contains("theorem __fact1"));
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn set_extension_combines_two_typed_subset_reflexivity_child_results() {
    let generated = compile_on_verifier_stack(
        "by extension {1} = {1}\n",
        "set_extension_recursive_result.lit",
    )
    .expect("compile set extension from its two typed subset-reflexivity child Results");
    assert!(generated.contains("Litex.Same.setExt"), "{generated}");
    assert_eq!(
        generated
            .matches("Litex.Set.subsetFromComplexMembershipImplication")
            .count(),
        2,
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn finite_set_enumeration_compiles_frozen_assignment_fact_ids_and_children() {
    let generated = compile_on_verifier_stack(
        "by enumerate finite_set:\n    ? forall x {1, 2}:\n        x = 1 or x = 2\n",
        "finite_set_enumeration_recursive_result.lit",
    )
    .expect("compile a finite enumeration from its assignment Results");
    assert!(generated.contains("__assignment_cases"), "{generated}");
    assert!(
        generated.contains("rcases __assignment_cases"),
        "{generated}"
    );
    assert!(generated.contains("Or.inl"), "{generated}");
    assert!(generated.contains("Or.inr"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn integer_range_iteration_compiles_evaluated_values_and_assignment_fact_ids() {
    let generated = compile_on_verifier_stack(
        "by for:\n    ? forall n range(0, 3):\n        n < 3\n",
        "integer_range_iteration_recursive_result.lit",
    )
    .expect("compile integer range iteration from recursive Results");
    assert!(generated.contains("__range_value_cases"), "{generated}");
    assert!(generated.contains("Finset.mem_Ico"), "{generated}");
    assert!(
        generated.contains("rcases __assignment_cases"),
        "{generated}"
    );
    assert!(
        generated.contains("⟨__range_value_case1, __assignment1⟩"),
        "{generated}"
    );
    assert!(generated.contains("Litex.In.congr"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn numeric_comparison_replays_prior_object_definition_results() {
    let generated = compile_on_verifier_stack(
        "have a R = 1\nhave b R = 2\na + b >= 0\n",
        "runtime_resolved_comparison_from_definition_results.lit",
    )
    .expect("compile Runtime-resolved comparison from exact definition Results");
    assert!(
        generated.contains("Litex.Nonnegative (a + b)"),
        "{generated}"
    );
    assert!(generated.contains("norm_num"), "{generated}");
    assert!(generated.contains("norm_num [a, b]"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.complexNegativeOneMulNonpositive (__fact4)"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn set_extension_compiles_nested_finite_enumeration_proof_steps() {
    let generated = compile_on_verifier_stack(
        "by extension:\n    ? {1, 2} = {2, 1}\n    by enumerate finite_set:\n        ? forall x {1, 2}:\n            x $in {2, 1}\n    by enumerate finite_set:\n        ? forall y {2, 1}:\n            y $in {1, 2}\n",
        "set_extension_with_finite_enumeration_results.lit",
    )
    .expect("compile set extension whose local proof steps are finite enumerations");
    assert!(generated.contains("Litex.Same.setExt"), "{generated}");
    assert!(
        generated.contains("Litex.Set.coproductEveryCarrierValueHasComplexRepresentative"),
        "{generated}"
    );
    assert_eq!(generated.matches("have __step").count(), 2, "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn nested_forall_premises_replay_parameter_aliases_and_normalization() {
    let generated = compile_on_verifier_stack(
        "forall h fn(x R) R:\n    forall y R:\n        h(y) = h(y - 1)\n    =>:\n        h(2) = h(1)\n",
        "nested_forall_probe.lit",
    )
    .expect("compile a nested forall premise");
    assert!(generated.contains("(__domain1 : ∀"), "{generated}");
    assert!(generated.contains("convert (__domain_f"), "{generated}");
    assert!(generated.contains("(__p1_s"), "{generated}");
    assert!(
        generated.contains("Litex.In.congr (Litex.Same.symm (Litex.Same.trans"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn compiler_core_keeps_representation_registry_closed() {
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("class PrimitiveRule"));
    assert!(core.contains("class DerivedRule"));
    assert!(core.contains("observationEq"));
    assert!(!core.contains("class BridgeRule"));
    assert!(!core.contains("def Bridge"));
    assert!(!core.contains("\naxiom "));
}

#[test]
fn compilation_report_is_transactional_and_marks_unsupported_result_routes() {
    let complete =
        compile_litex_source_to_lean_compilation_report("1 = 1\n", "complete_report.lit")
            .expect("capture and emit a complete report");
    assert_eq!(complete.status, StmtResultToLeanCompilationStatus::Complete);
    assert!(complete.is_complete());
    assert!(complete.unsupported.is_empty());
    assert!(complete.lean_code.contains("theorem __fact0"));

    let incomplete =
        compile_litex_source_to_lean_compilation_report("1 != 0\n", "incomplete_report.lit")
            .expect(
            "successful Result with an unsupported Lean-source construction route returns a report",
        );
    assert_eq!(
        incomplete.status,
        StmtResultToLeanCompilationStatus::Incomplete
    );
    assert!(!incomplete.is_complete());
    assert_eq!(incomplete.unsupported.len(), 1);
    assert_eq!(
        incomplete.unsupported[0].phase,
        StmtResultToLeanCompilationPhase::LeanSourceConstruction
    );
    assert!(incomplete
        .lean_code
        .contains("StmtResult-to-Lean compilation incomplete"));
    assert!(!incomplete.lean_code.contains("theorem __fact0"));
    assert!(!incomplete.lean_code.contains("axiom "));
}

#[test]
fn set_tracer_consumes_verified_equality_rewrite_result() {
    let generated = compile_on_verifier_stack(
        "sketch:\n    have A set = R\n    have B set = C\n    forall a A, b B:\n        a = b\n        =>:\n            b $in A\n            a $in B\n    1 = 1\n",
        "1_SetSystem.lit",
    )
    .expect("compile set tracer");
    assert!(generated.contains("abbrev A : Litex.Set := Litex.R"));
    assert!(generated.contains("abbrev B : Litex.Set := Litex.C"));
    assert!(generated.contains("Litex.In.congr"));
    assert!(generated.contains("Litex.Same __p1 __p2"));
    assert!(generated.contains("Litex.Same (1 : ℂ) (1 : ℂ)"));
    assert!(generated.contains("namespace __Sketch01"));
    assert!(generated.contains("end __Sketch01"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn order_tracer_compiles_catalog_rule_and_rejects_non_catalog_transitivity() {
    const SOURCE: &str = include_str!("../../lean/examples/2_OrderSystem.lit");
    let generated = compile_on_verifier_stack(SOURCE, "2_OrderSystem.lit")
        .expect("compile catalog strict-to-weak order rule");
    assert!(generated.contains("Litex.Lt.toLe (__domain_f"));
    assert!(generated.contains("Litex.Lt.toLe (__domain_f"));
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("sorry"));

    let transitivity = compile_on_verifier_stack(
        "sketch:\n    forall a, b, c R:\n        a < b\n        b < c\n        =>:\n            a < c\n",
        "2_OrderSystemTransitivityBoundary.lit",
    )
    .expect("compile the typed strict-order transitivity Result");
    assert!(
        transitivity.contains("Litex.Lt.trans (__domain_f"),
        "{transitivity}"
    );

    let boundary = compile_on_verifier_stack(
        "sketch:\n    forall a, b C:\n        a < b\n        =>:\n            a <= b\n",
        "unsupported_complex_order.lit",
    )
    .expect_err("C-only order must remain outside the source ordered-real fragment");
    assert!(boundary.contains("ordered comparison requires both operands to belong to R"));
}

#[test]
fn top_level_atomic_equality_compiles_typed_result_evidence() {
    let generated =
        compile_on_verifier_stack("1 = 1\n2 + 3 = 5\n2 + 3 = 5\n", "3_AtomicEquality.lit")
            .expect("compile top-level atomic equality tracer");
    assert!(generated.contains("Litex.Same.refl (1 : ℂ)"));
    assert!(generated.contains("Litex.Same ((2 : ℂ) + (3 : ℂ)) (5 : ℂ)"));
    assert!(generated.contains(
        "Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])"
    ));
    assert!(generated.contains("theorem __fact2"));
    assert!(generated.contains("exact __fact1"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn complex_algebraic_normalization_records_typed_boundary_rule_id() {
    const SOURCE: &str = include_str!("../../lean/examples/54_ComplexAlgebraicCalculation.lit");
    const BOUNDARY_SOURCE: &str = "1 / i = -1 * i\n";
    let result_json = capture_statement_results_json_on_verifier_stack(
        SOURCE,
        "54_ComplexAlgebraicCalculation.lit",
    )
    .expect("capture complex-algebraic-normalization statement-result JSON");
    assert_eq!(
        result_json.matches("ComplexAlgebraicNormalization").count(),
        3,
        "{result_json}"
    );
    assert!(
        result_json.contains("RationalAlgebraicNormalization"),
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "54_ComplexAlgebraicCalculation.lit")
        .expect("compile supported complex-algebraic normalization routes");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");

    let boundary_json = capture_statement_results_json_on_verifier_stack(
        BOUNDARY_SOURCE,
        "54_ComplexAlgebraicCalculationBoundary.lit",
    )
    .expect("capture typed native-i nonzero boundary evidence");
    assert!(boundary_json.contains(
        "\"rule_id\": \"builtin.verify.verify_builtin_rules.complex_builtin.try_verify_native_i_nonzero\""
    ));

    let error = compile_on_verifier_stack(
        BOUNDARY_SOURCE,
        "54_ComplexAlgebraicCalculationBoundary.lit",
    )
    .expect_err("uncatalogued native-i nonzero evidence must fail closed");
    assert!(
        error.contains(
            "builtin.verify.verify_builtin_rules.complex_builtin.try_verify_native_i_nonzero"
        ),
        "{error}"
    );
}

#[test]
fn complex_algebraic_normalization_keeps_missing_nonzero_premise_fail_closed() {
    let error = compile_on_verifier_stack(
        "forall z C:\n    (z + i) ^ 2 / (z + i) = z + i\n",
        "complex_missing_nonzero_premise.lit",
    )
    .expect_err("division without a nonzero premise must remain ill-defined");
    assert!(error.contains("divisor `"), "{error}");
    assert!(error.contains("z + i` must be non-zero"), "{error}");
}

#[test]
fn top_level_atomic_membership_emits_source_and_inferred_fact_ids() {
    let generated = compile_on_verifier_stack("2 + 3 $in N\n", "atomic_membership.lit")
        .expect("compile top-level atomic membership");
    assert!(generated.contains("Litex.In ((2 : ℂ) + (3 : ℂ)) Litex.N"));
    assert!(generated.contains("Litex.Rules.complexEqNatInN ((2 : ℂ) + (3 : ℂ)) 5 (by norm_num)"));
    assert!(generated.contains("Litex.Nonnegative ((2 : ℂ) + (3 : ℂ))"));
    assert!(generated.contains("Litex.Rules.nonnegativeOfInN (__fact0)"));
    assert!(!generated.contains("Litex.OrderBridge.nonnegativeOfComplexReal (by norm_num)"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn top_level_recursive_inference_theorems_close_over_earlier_inference_steps() {
    let generated = compile_on_verifier_stack("1 $in N\n", "recursive_membership_inference.lit")
        .expect("compile recursive top-level membership inference");
    assert!(generated.contains("theorem __fact2"), "{generated}");
    assert!(generated.contains("have __infer1_0"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.complexNegativeOneMulNonpositive (__infer1_0)"),
        "{generated}"
    );
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn inference_compilation_does_not_parse_rendered_lean_statements() {
    const COMPILER_SOURCES: &[&str] = &[
        include_str!("../../src/stmt_result_to_lean_compiler/file_compilation.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/markdown_compilation.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/source_compilation.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/target_types.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/function_contracts.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/object_representation.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/compilation_report.rs"),
        include_str!("../../src/stmt_result_to_lean_compiler/compiler/state.rs"),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/algebraic_normalization.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/chain_inference_projections.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/defined_predicate_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/direct_fact_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/direct_membership_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/inference_environment.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/local_inference_state.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/local_inference_statements.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/numeric_membership_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/object_reflexivity.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/statement_dispatch.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/stored_fact_citations.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/transitive_predicate_chains.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/tuple_equality_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/typed_inference_declarations.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/universal_facts.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/fact_compilation/well_definedness_rendering.rs"),
        ),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/definition_proofs.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/evaluation.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/function_equalities.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/local_objects.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/matrices.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/nonempty_objects.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/object_equalities.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/proposition_definitions.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/sequences.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/speculative_execution.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/trust_statements.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/object_definitions/tuples.rs"),
        ),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/abstract_predicate_definitions.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/exact_predicate_transport.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/fact_citations.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/forall_parameters.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/function_reduction.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/inference_ownership.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/inference_validation.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/list_set_elimination.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/numeric_comparison.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/numeric_membership.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/numeric_sign_rendering.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/object_values.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/power_membership_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/predicate_arguments.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/rational_normalization.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/registered_predicate_properties.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/representative_transport.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/set_algebra_rules.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/set_builder_membership.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/standard_set_projection.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/proof_rendering/structural_set_equality.rs"),
        ),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/aggregate_objects.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/builtin_objects.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/existential_facts.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/fact_components.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/fact_rendering.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/function_applications.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/function_types.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/function_values.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/list_sets.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/logical_connectives.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/numeric_objects.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/numeric_set_certificates.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/object_rendering.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/parameter_contracts.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/source_text.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/standard_sets.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/structured_induction.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/target_sets.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/source_rendering/typed_spines.rs"),
        ),
        include_str!("../../src/stmt_result_to_lean_compiler/compiler/structured_proofs.rs"),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/builtin_theorem_application.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/cartesian_inference.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/claims.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/examples.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/fact_goal_proofs.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/local_definition_steps.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/local_fact_steps.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/local_forall_steps.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/local_statement_steps.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/named_forall.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/named_theorems.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/real_analysis_builtins.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/registered_predicate_properties.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/sketches.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/strategies_and_settings.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/templates.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/theorem_instantiation.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/theorem_compilation/theorem_selection.rs"),
        ),
        concat!(
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/mod.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/definition_types.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/direct_compilation_audit.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/fact_context_collection.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/fact_publication.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/fact_store_results.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/fact_well_definedness.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/inference_identity.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/object_context_collection.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/object_result_validation.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/range_loops.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/standard_set_nonempty.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/template_instantiation.rs"),
            include_str!("../../src/stmt_result_to_lean_compiler/compiler/validation/well_definedness_installation.rs"),
        ),
        include_str!("../../src/stmt_result_to_lean_compiler/environment.rs"),
    ];
    for forbidden_parser in [
        "strip_prefix(\"have \")",
        "split_once(\" : \")",
        "split_once(\" := \")",
    ] {
        assert!(
            COMPILER_SOURCES
                .iter()
                .all(|source| !source.contains(forbidden_parser)),
            "compiler must keep inference identity and proof fields structured instead of using `{forbidden_parser}`"
        );
    }
    assert!(COMPILER_SOURCES
        .iter()
        .any(|source| source.contains("CompiledInferenceFactProofStep")));
}

#[test]
fn native_constants_use_mathlib_terms_and_exact_membership_rules() {
    const SOURCE: &str = "i = i\ne = e\npi = pi\n\ni $in C\ne $in R\npi $in R\ne $in C\npi $in C\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "19_NativeConstants.lit")
            .expect("capture native-constant statement-result JSON");
    for evidence in [
        "ImaginaryUnitInComplex",
        "EulerNumberInReal",
        "PiInReal",
        "StandardSetMembershipProjection",
    ] {
        assert!(
            result_json.contains(evidence),
            "missing {evidence}: {result_json}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "19_NativeConstants.lit")
        .expect("compile native-constant tracer");
    for term in ["Complex.I", "((Real.exp 1 : ℝ) : ℂ)", "((Real.pi : ℝ) : ℂ)"] {
        assert!(generated.contains(term), "missing {term}: {generated}");
    }
    for theorem in ["imaginaryUnitInC", "eInR", "piInR", "inCOfInR"] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn standard_set_hierarchy_replays_exact_projection_chain() {
    const SOURCE: &str = "forall n N:\n    n $in Z\n\nforall n N:\n    n $in Q\n\nforall n N:\n    n $in R\n\nforall n N:\n    n $in C\n\nforall z Z:\n    z $in Q\n\nforall z Z:\n    z $in R\n\nforall z Z:\n    z $in C\n\nforall q Q:\n    q $in R\n\nforall q Q:\n    q $in C\n\nforall r R:\n    r $in C\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "16_StandardSetHierarchy.lit")
            .expect("capture standard-set hierarchy statement-result JSON");
    assert_eq!(
        result_json
            .matches("StandardSetMembershipProjection")
            .count(),
        10,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "16_StandardSetHierarchy.lit")
        .expect("compile standard-set hierarchy tracer");
    for theorem in ["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn positive_natural_uses_exact_subtype_and_projection() {
    const SOURCE: &str = "1 $in N+\n\nforall n N+:\n    n $in N\n";
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("abbrev NPos : Litex.Set := setBuilder N (fun n => 0 < n)"));

    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "20_PositiveNaturalCarrier.lit")
            .expect("capture positive-natural statement-result JSON");
    assert!(
        result_json.contains("ClosedNumericMembership"),
        "{result_json}"
    );
    assert!(
        result_json.contains("StandardSetMembershipProjection"),
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "20_PositiveNaturalCarrier.lit")
        .expect("compile positive-natural tracer");
    for expected in [
        "Litex.In (1 : ℂ) Litex.NPos",
        "Litex.Rules.complexEqNatInNPos (1 : ℂ) 1 (by norm_num) (by norm_num)",
        "Litex.Rules.inNOfInNPos",
        "have __infer",
        "Litex.Rules.positiveNaturalRepPositive (__h",
    ] {
        assert!(
            generated.contains(expected),
            "missing {expected}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn positive_real_uses_exact_projection_and_uncatalogued_constructor_fails_closed() {
    const SOURCE: &str =
        "1 $in R+\ne $in R+\npi $in R+\n\nforall r R+:\n    r $in R\n    r $in C\n    r > 0\n";
    const BOUNDARY_SOURCE: &str = "forall r R:\n    r > 0\n    =>:\n        r $in R+\n";
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("abbrev RPos : Litex.Set := setBuilder R (fun r => 0 < r)"));

    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "21_PositiveRealCarrier.lit")
            .expect("capture positive-real statement-result JSON");
    for expected in [
        "ClosedNumericMembership",
        "EulerNumberInPositiveReal",
        "PiInPositiveReal",
        "StandardSetMembershipProjection",
    ] {
        assert!(
            result_json.contains(expected),
            "missing {expected}: {result_json}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "21_PositiveRealCarrier.lit")
        .expect("compile positive-real tracer");
    for expected in [
        "Litex.Rules.complexEqRealInRPos (1 : ℂ) (1 : ℝ)",
        "Litex.Rules.eInRPos",
        "Litex.Rules.piInRPos",
        "Litex.Rules.inROfInRPos",
        "Litex.Rules.inCOfInR",
        "Litex.Rules.positiveOfInRPos",
        "have __infer",
        "Litex.Rules.positiveRealRepPositive (__h",
    ] {
        assert!(
            generated.contains(expected),
            "missing {expected}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary_json = capture_statement_results_json_on_verifier_stack(
        BOUNDARY_SOURCE,
        "unsupported_generic_r_pos_constructor.lit",
    )
    .expect("generic R+ construction verifies with typed Rust evidence");
    assert!(boundary_json.contains("\"kind\": \"Uncatalogued\""));
    assert!(boundary_json.contains(
        "\"rule_id\": \"builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_values.number_in_set_verified_by_builtin_rules_result_with_subgoals\""
    ));

    let boundary =
        compile_on_verifier_stack(BOUNDARY_SOURCE, "unsupported_generic_r_pos_constructor.lit")
            .expect_err("generic R+ construction still needs representative coherence");
    assert!(
        boundary.contains(
            "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_values.number_in_set_verified_by_builtin_rules_result_with_subgoals"
        ),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn rational_positive_and_negative_numeric_carriers_compile_typed_sign_inference() {
    const SOURCE: &str = "1 $in Q+\n-1 $in Z-\n-2 $in Q-\n-3 $in R-\n";
    let generated = compile_on_verifier_stack(SOURCE, "signed_refined_numeric_carriers.lit")
        .expect("compile all checked positive/negative refined numeric carriers");

    for expected in [
        "Litex.Rules.complexEqRatInQPos",
        "Litex.Rules.complexEqIntInZNeg",
        "Litex.Rules.complexEqRatInQNeg",
        "Litex.Rules.complexEqRealInRNeg",
        "Litex.Rules.positiveOfInQPos",
        "Litex.Rules.negativeOfInZNeg",
        "Litex.Rules.negativeOfInQNeg",
        "Litex.Rules.negativeOfInRNeg",
        "Litex.Negative",
    ] {
        assert!(
            generated.contains(expected),
            "missing {expected}: {generated}"
        );
    }
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn nonzero_numeric_carriers_replay_exact_constructors_and_widening() {
    const SOURCE: &str = include_str!("../../lean/examples/22_NonzeroNumericCarriers.lit");
    let core = include_str!("../../lean/Litex/Core.lean");
    for (carrier, base) in [
        ("ZStar", "Z"),
        ("QStar", "Q"),
        ("RStar", "R"),
        ("CStar", "C"),
    ] {
        assert!(
            core.contains(&format!("abbrev {carrier} : Litex.Set :="))
                && core.contains(&format!("setBuilder C (fun z => In z {base} ∧"))
                && core.contains("(ComplexObserver.none ℂ) (ComplexObserver.none ℂ) z (0 : ℂ)"),
            "missing exact {carrier} carrier"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "22_NonzeroNumericCarriers.lit")
        .expect("compile nonzero numeric-carrier tracer");
    for theorem in [
        "inZStarOfInZNotSameZero",
        "inQStarOfInQNotSameZero",
        "inRStarOfInRNotSameZero",
        "inCStarOfInCNotSameZero",
        "inZOfInZStar",
        "inQOfInQStar",
        "inROfInRStar",
        "inCOfInCStar",
        "inQStarOfInZStar",
        "inRStarOfInQStar",
        "inCStarOfInRStar",
        "notSameZeroOfInZStar",
        "notSameZeroOfInQStar",
        "notSameZeroOfInRStar",
        "notSameZeroOfInCStar",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(
        generated.contains(
            "(Litex.Rules.notSameZeroOfInCStar (__membership)) (Litex.Same.reflNoObservation (0 : ℂ))"
        ),
        "closed C* nonmembership did not compile from its direct Result evidence: {generated}"
    );
    assert!(generated.contains("have __infer"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.notSameZeroOfInZStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInQStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInRStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInCStar (__h"),
        "nonzero inference did not stay inside its forall frames: {generated}"
    );
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack("1 $in Z*\n", "unsupported_closed_z_star.lit")
        .expect_err("standalone closed star reflection remains fail-closed");
    assert!(
        boundary.contains("closed comparison")
            || boundary.contains("unsupported inferred proof")
            || boundary.contains("has no supported Litex-to-Lean proof rule")
            || boundary.contains("Z*"),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn numeric_carrier_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b C:\n    a + b $in C\n\nforall a, b C:\n    a - b $in C\n\nforall a, b C:\n    a * b $in C\n\nforall a, b C:\n    b != 0\n    =>:\n        a / b $in C\n\nforall a, b Z:\n    a + b $in Z\n\nforall a, b Z:\n    a - b $in Z\n\nforall a, b Z:\n    a * b $in Z\n\nforall a, b Z:\n    b != 0\n    =>:\n        a % b $in Z\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "17_NumericCarrierClosures.lit")
            .expect("capture numeric carrier-closure statement-result JSON");
    assert_eq!(
        result_json
            .matches("ComplexArithmeticMembershipClosure")
            .count(),
        4,
        "{result_json}"
    );
    assert_eq!(
        result_json.matches("IntegerMembershipClosure").count(),
        4,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "17_NumericCarrierClosures.lit")
        .expect("compile numeric carrier-closure tracer");
    for theorem in [
        "complexAddInC",
        "complexSubInC",
        "complexMulInC",
        "complexDivInC",
        "complexAddInZ",
        "complexSubInZ",
        "complexMulInZ",
        "complexIntInZ",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
    assert!(
        generated.contains("∀ (__p1 : ℤ) (__p2 : ℤ)")
            && generated.contains("Litex.Rules.complexIntInZ (a % b)"),
        "integer remainder did not preserve its native integer binders: {generated}"
    );
    assert!(!generated.contains("Litex.In.rep a __h7_1"));
}

#[test]
fn rational_and_natural_carrier_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b Q:\n    a + b $in Q\n\nforall a, b Q:\n    a - b $in Q\n\nforall a, b Q:\n    a * b $in Q\n\nforall a, b Q:\n    b != 0\n    =>:\n        a / b $in Q\n\nforall a, b N:\n    a + b $in N\n\nforall a, b N:\n    a * b $in N\n\nforall a Q, z Z:\n    a != 0\n    =>:\n        a^z $in Q\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "18_RationalNaturalClosures.lit")
            .expect("capture rational/natural carrier-closure statement-result JSON");
    assert_eq!(
        result_json.matches("RationalMembershipClosure").count(),
        5,
        "{result_json}"
    );
    assert_eq!(
        result_json.matches("NaturalMembershipClosure").count(),
        2,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "18_RationalNaturalClosures.lit")
        .expect("compile rational/natural carrier-closure tracer");
    for theorem in [
        "complexAddInQ",
        "complexSubInQ",
        "complexMulInQ",
        "complexDivInQ",
        "complexAddInN",
        "complexMulInN",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
    assert!(generated.matches("have __infer4_").count() >= 4);
    assert!(generated.matches("have __infer5_").count() >= 4);
    assert!(generated.contains("Litex.Rules.nonnegativeOfInN"));
    assert!(generated.contains("Litex.Rules.complexEqNatInN"));
    assert!(!generated.contains("complexAddInN (__h4_1)"));
    assert!(!generated.contains("complexMulInN (__h5_1)"));
    assert!(
        generated.contains("Litex.In.rep a __h")
            && generated.contains("(__p2 : ℤ)")
            && generated.contains("Litex.Rules.complexRatInQ")
            && generated.contains(" ^ z : ℚ"),
        "rational power did not preserve its exact Q representative and native Z exponent: {generated}"
    );
}

#[test]
fn known_equality_paths_replay_same_symmetry_and_transitivity() {
    const SOURCE: &str = "forall a, b set:\n    a = b\n    =>:\n        b = a\n\nforall a, b, c set:\n    a = b\n    b = c\n    =>:\n        a = c\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "known_equality.lit")
            .expect("capture exact known-equality Result paths");
    assert!(result_json.contains("ForallProof"));
    assert!(result_json.contains("KnownEqualityPath"));
    assert!(result_json.contains("source_fact_id"));
    assert!(!result_json.contains("BuiltinStrategy"));

    let generated = compile_on_verifier_stack(SOURCE, "known_equality.lit")
        .expect("compile exact known-equality paths");
    assert!(generated.contains("Litex.Same.symm (__domain_f"));
    assert!(generated.contains("Litex.Same.trans (__domain_f"));
    assert!(!generated.contains("Eq.symm"));
    assert!(!generated.contains("Eq.trans"));
}

#[test]
fn not_equal_symmetry_negates_heterogeneous_same() {
    let generated = compile_on_verifier_stack(
        "forall a, b set:\n    a != b\n    =>:\n        b != a\n",
        "not_equal_symmetry.lit",
    )
    .expect("compile not-equality symmetry");
    assert!(generated.contains("(__domain1 : ¬ @Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) __p1 __p2)"));
    assert!(generated.contains(
        "¬ @Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) b a"
    ));
    assert!(generated.contains("Litex.Rules.notSameSymm (__domain_f"));
}

#[test]
fn conjunction_disjunction_and_alpha_forall_citations_replay_exact_evidence() {
    let generated = compile_on_verifier_stack(
        "1 = 1 and 2 = 2\n\nforall a, b set:\n    a = a\n    b = b\n    =>:\n        a = a and b = b\n\nforall a, b set:\n    a = a\n    =>:\n        a = a or b = b\n\nforall x, y set:\n    x = y\n    =>:\n        y = x\n\nforall a, b set:\n    a = b\n    =>:\n        b = a\n",
        "propositional_fact_spine.lit",
    )
    .expect("compile propositional proof spine");
    assert!(generated.contains("(Litex.Same (1 : ℂ) (1 : ℂ)) ∧ (Litex.Same (2 : ℂ) (2 : ℂ))"));
    assert!(generated.contains("exact ⟨Litex.Same.refl (1 : ℂ), Litex.Same.refl (2 : ℂ)⟩"));
    assert!(generated
        .contains("have __prior1_0 : (Litex.Same a a) ∧ (Litex.Same b b) := ⟨Litex.Same.refl"));
    assert!(generated.contains("exact __prior1_0"));
    assert!(generated
        .contains("have __prior2_0 : Litex.Same a a ∨ Litex.Same b b := Or.inl (Litex.Same.refl"));
    assert!(generated.contains("exact __prior2_0"));
    assert!(generated.contains("theorem __fact4 :\n    ∀ (__p1 : Litex.Set) (__p2 : Litex.Set)"));
    assert!(generated.contains(":= __fact3"));
}

#[test]
fn conjunction_projection_replays_inferred_fact_ids() {
    let generated = compile_on_verifier_stack(
        "forall a, b, c, d set:\n    a != b and c != d\n    =>:\n        c != d\n",
        "conjunction_projection.lit",
    )
    .expect("compile conjunction projection proof spine");
    assert!(generated.contains("have __infer0_0 : ¬ @Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) a b := (__domain_f"));
    assert!(generated.contains("have __infer0_1 : ¬ @Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) c d := (__domain_f"));
    assert!(generated.contains("have __prior0_0"));
    assert!(generated.contains(":= __infer0_1"));
    assert!(generated.contains("exact __prior0_0"));
}

#[test]
fn unary_function_set_application_consumes_both_memberships() {
    let generated = compile_on_verifier_stack(
        "forall s, S set, x s, f fn(y s) S:\n    f(x) = f(x)\n",
        "4_FunctionSet.lit",
    )
    .expect("compile unary function-set tracer");
    assert!(generated.contains("import Litex\n"));
    assert!(!generated.contains("import Litex.Rules\n"));
    assert!(generated.contains("(__p1 : Litex.Set)"));
    assert!(generated.contains("(__p2 : Litex.Set)"));
    assert!(generated.contains("Litex.In __p3 __p1"), "{generated}");
    assert!(
        generated.contains("__type4 : Litex.In (α :="),
        "{generated}"
    );
    assert!(generated.contains("Litex.fnApplyOwn (domain := s) (codomain := S) f"));
    assert!(generated.contains("__type4"));
    assert!(!generated.contains("namespace __Sketch"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multilayer_application_preserves_each_unary_source_contract() {
    const SOURCE: &str =
        "forall S, T, U set, a S, b T, g fn(x S) fn(y T) U:\n    g(a)(b) = g(a)(b)\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "23_MultilayerApplication.lit")
            .expect("capture multi-layer application statement-result JSON");
    assert!(
        result_json.contains("\"through_layer_index\": 0"),
        "{result_json}"
    );
    assert!(result_json.contains("\"layer_index\": 0"), "{result_json}");
    assert!(result_json.contains("\"layer_index\": 1"), "{result_json}");

    let generated = compile_on_verifier_stack(SOURCE, "23_MultilayerApplication.lit")
        .expect("compile multi-layer application tracer");
    assert!(generated.contains("__type6 : Litex.In (α :="));
    assert!(generated.contains("let __fn_layer1 := (Litex.fnApplyOwn (domain :="));
    assert!(generated.contains("Litex.fnApplyOwn (domain := T) (codomain := U) __fn_layer1"));
    assert!(generated.contains("(Litex.In.own (Litex.fnSet"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));

    const THREE_LAYERS: &str = "forall S, T, U, V set, a S, b T, c U, g fn(x S) fn(y T) fn(z U) V:\n    g(a)(b)(c) = g(a)(b)(c)\n";
    let generated = compile_on_verifier_stack(THREE_LAYERS, "three_layer_application.lit")
        .expect("compile three source application layers");
    assert!(generated.contains("let __fn_layer2 :="));
    assert!(generated.contains("Litex.fnApplyOwn (domain := U) (codomain := V) __fn_layer2"));
    assert!(generated.contains("(U : Litex.Set.{0}) (V : Litex.Set.{0})"));

    const SAME_LAYER: &str =
        "forall S, T, U set, a S, b T, f fn(x S, y T) U:\n    f(a, b) = f(a, b)\n";
    let same_layer_result_json = capture_statement_results_json_on_verifier_stack(
        SAME_LAYER,
        "23_MultilayerApplication.lit",
    )
    .expect("capture same-layer telescope statement-result JSON");
    assert!(same_layer_result_json.contains("\"parameter_index\": 0"));
    assert!(same_layer_result_json.contains("\"parameter_index\": 1"));
    let same_layer = compile_on_verifier_stack(SAME_LAYER, "23_MultilayerApplication.lit")
        .expect("compile one exact two-parameter source layer");
    assert!(same_layer.contains("Litex.fnTelescopeSet"));
    assert!(same_layer.contains("Litex.FnTelescope.parameter"));
    assert!(same_layer.contains("Litex.fnTelescopeApplyOwn (signature :="));
    assert!(same_layer.contains(").down"));
    assert!(!same_layer.contains("Litex.Object"));
    assert!(!same_layer.contains("sorry"));

    const SAME_LAYER_DOMAIN: &str = "forall f fn(x, y R: x > 0, y > 0) R, a, b R:\n    a > 0\n    b > 0\n    =>:\n        f(a, b) = f(a, b)\n";
    let same_layer_domain =
        compile_on_verifier_stack(SAME_LAYER_DOMAIN, "23_MultilayerApplication.lit")
            .expect("compile same-layer ordered domain clauses");
    assert!(same_layer_domain.contains("Litex.FnTelescope.requirement"));
    assert!(
        same_layer_domain.contains("Litex.Lt (0 : ℂ) (((Litex.In.rep __arg1 __arg1_in : ℝ)) : ℂ)")
    );
    assert!(
        same_layer_domain.contains("Litex.Lt (0 : ℂ) (((Litex.In.rep __arg2 __arg2_in : ℝ)) : ℂ)")
    );
    assert!(same_layer_domain.contains("__domain1"));
    assert!(same_layer_domain.contains("__domain2"));
    assert!(same_layer_domain.contains("⟨__domain_f"));

    let split = compile_on_verifier_stack(
        "forall S, T, U set, a S, b T, f fn(x S, y T) U:\n    f(a)(b) = f(a)(b)\n",
        "split_same_layer_application.lit",
    )
    .expect_err("a source layer must not be repaired by target currying");
    assert!(
        split.contains("parameter")
            || split.contains("well-defined")
            || split.contains("cannot verify"),
        "unexpected split-layer error: {split}"
    );
}

#[test]
fn dependent_function_sets_keep_parameter_and_return_carriers() {
    const DEPENDENT_PARAMETER: &str = "forall f fn(x R, y {z R: z > x}) R:\n    f = f\n";
    let parameter =
        compile_on_verifier_stack(DEPENDENT_PARAMETER, "24_DependentAnonymousFunction.lit")
            .expect("compile a parameter set depending on an earlier source parameter");
    assert!(parameter.contains("Litex.fnTelescopeSet"), "{parameter}");
    assert!(
        parameter.contains("Litex.In.rep __arg1 __arg1_in"),
        "{parameter}"
    );
    assert!(parameter.contains("Litex.Lt"), "{parameter}");

    const DEPENDENT_RETURN: &str = "forall f fn(x R) {z R: z > x}, a R:\n    f(a) = f(a)\n";
    let returned = compile_on_verifier_stack(DEPENDENT_RETURN, "24_DependentAnonymousFunction.lit")
        .expect("compile an application with an argument-indexed exact return set");
    assert!(returned.contains("Litex.fnTelescopeSet"), "{returned}");
    assert!(
        returned.contains("Litex.fnTelescopeApplyOwn (signature :="),
        "{returned}"
    );
    assert!(returned.contains("Litex.setBuilder Litex.R"), "{returned}");
    assert!(returned.contains(").down"), "{returned}");
    assert!(!returned.contains("Litex.Object"));
    assert!(!returned.contains("sorry"));
}

#[test]
fn compound_anonymous_functions_replay_their_owned_wd_scope() {
    const SOURCE: &str = "fn(x R) R {x + 1} = fn(y R) R {y + 1}\n\nforall a R:\n    fn(x R) R {x + 1}(a) = fn(x R) R {x + 1}(a)\n";
    let result_json = capture_statement_results_json_on_verifier_stack(
        SOURCE,
        "24_DependentAnonymousFunction.lit",
    )
    .expect("capture compound anonymous-function WD statement-result JSON");
    assert!(
        result_json.contains("AnonymousFunctionBodyMembership"),
        "{result_json}"
    );
    assert!(result_json.contains("AnonymousFunction"), "{result_json}");
    assert!(result_json.contains("FunctionHead"), "{result_json}");

    let generated = compile_on_verifier_stack(SOURCE, "24_DependentAnonymousFunction.lit")
        .expect("compile compound anonymous values and their direct application");
    assert!(
        generated.contains("((Litex.In.rep __arg __arg_in : ℝ) + (1 : ℝ))"),
        "{generated}"
    );
    assert!(generated.contains("Litex.fnApplyCarrier"), "{generated}");
    assert!(
        generated.contains("Litex.In.own (Litex.fnSet"),
        "{generated}"
    );
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack(
        "fn(x R) N {x} = fn(y R) N {y}\n",
        "unsupported_anonymous_return.lit",
    )
    .expect_err("an anonymous body without checked return membership must be rejected");
    assert!(boundary.contains("not verified to belong to defined return set"));
}

#[test]
fn sketch_compiles_to_an_isolated_namespace() {
    let generated =
        compile_on_verifier_stack("1 = 1\nsketch:\n    2 = 2\n3 = 3\n", "sketch_namespace.lit")
            .expect("compile sketch namespace tracer");
    assert!(generated.contains("namespace __Sketch01"));
    assert!(generated.contains("end __Sketch01"));
    assert_eq!(generated.matches("theorem __fact0").count(), 2);
    assert!(generated.contains("theorem __fact1 : Litex.Same (3 : ℂ) (3 : ℂ)"));
    assert!(!generated.contains("theorem __fact2"));
}

#[test]
fn function_application_without_domain_membership_is_rejected_by_litex() {
    let error = compile_on_verifier_stack(
        "forall s, S set, x S, f fn(y s) S:\n    f(x) = f(x)\n",
        "function_without_domain_membership.lit",
    )
    .expect_err("Litex must reject an application without x in s");
    assert!(
        error.contains("not in") || error.contains("well-defined") || error.contains("verify"),
        "unexpected error: {error}"
    );
}

#[test]
fn unsupported_atomic_predicate_fails_closed() {
    let error = compile_on_verifier_stack("1 != 0\n", "unsupported.lit")
        .expect_err("unsupported fact must fail closed");
    assert!(error.contains(
        "closed comparison requires an order relation; closed equality and disequality use separate semantic adapters"
    ));
}

#[test]
fn proof_scope_tracer_emits_named_theorem_claim_and_example() {
    let generated = compile_on_verifier_stack(
        "thm one_eq_one:\n    ? forall:\n        1 = 1\n\nclaim:\n    ? 2 = 2\n    2 = 2\n\nexample:\n    ? 3 = 3\n    3 = 3\n",
        "8_ProofScopes.lit",
    )
    .expect("compile proof-scope tracer");
    assert!(generated.contains("theorem one_eq_one :"));
    assert!(generated.contains("theorem __fact1 : Litex.Same (2 : ℂ) (2 : ℂ)"));
    assert!(generated.contains("example : Litex.Same (3 : ℂ) (3 : ℂ)"));
    assert!(generated.contains("have __step1_0 : Litex.Same (2 : ℂ) (2 : ℂ)"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn cases_and_contradiction_replay_branch_local_fact_ids() {
    let generated = compile_on_verifier_stack(
        "thm cases_and_contra:\n    ? forall:\n        2 = 2\n    by cases:\n        ? 1 = 1\n        case 1 = 1:\n            by contra:\n                ? 2 = 2\n                impossible 2 != 2\n",
        "9_CasesAndContradiction.lit",
    )
    .expect("compile cases-and-contradiction tracer");
    assert!(generated.contains("theorem cases_and_contra :"));
    assert!(generated.contains("have __case1"));
    assert!(generated.contains("by_contra __reverse"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn structured_and_nested_case_scopes_compile_recursive_result_fields() {
    const STRUCTURED: &str = "by cases:\n    ? 2 = 2\n    case 1 = 1 and 2 = 2:\n        1 = 1\nby contra:\n    ? not 2 < 1\n    impossible 2 < 1\n";
    let structured = compile_on_verifier_stack(STRUCTURED, "9_CasesAndContradiction.lit")
        .expect("compile conjunction assumptions and a negative contradiction goal");
    assert!(
        structured.contains("have __case1_component1"),
        "{structured}"
    );
    assert!(
        structured.contains("have __case1_component2"),
        "{structured}"
    );
    assert!(
        structured.contains("Classical.byContradiction"),
        "{structured}"
    );

    const NESTED: &str = "have fn identity(x R) R = x\nby cases:\n    ? identity(1) = identity(1)\n    case 1 = 1:\n        by contra:\n            ? 2 = 2\n            impossible 2 != 2\n        1 $in R\nby contra:\n    ? 3 = 3\n    by cases:\n        ? 4 = 4\n        case 4 = 4:\n            5 = 5\n    impossible 3 != 3\n";
    let nested = compile_on_verifier_stack(NESTED, "nested_case_scope.lit")
        .expect("compile nested case/contradiction scopes with branch-local WD");
    assert!(
        nested.matches("by_contra __reverse").count() >= 2,
        "{nested}"
    );
    assert!(
        nested.contains("Litex.fnApplyCarrier (domain := Litex.R)"),
        "{nested}"
    );
    assert!(!nested.contains("sorry"));

    let reused = compile_on_verifier_stack(
        "2 = 2\nby contra:\n    ? 2 = 2\n    impossible 2 != 2\n",
        "reused_by_contra_goal.lit",
    )
    .expect("compile an explicit proof whose already-known goal receives no new FactId");
    assert_eq!(reused.matches("theorem __fact").count(), 1, "{reused}");
}

#[test]
fn existential_intro_and_elim_use_native_carrier_and_exact_projections() {
    let generated = compile_on_verifier_stack(
        "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\ny = 1\n",
        "10_ExistentialWitness.lit",
    )
    .expect("compile existential introduction/elimination tracer");
    assert!(generated.contains(
        "∃ (x : (Litex.R).Carrier), ∃ (__type_x : Litex.In x Litex.R), Litex.Same x (1 : ℂ)"
    ));
    assert!(generated.contains("noncomputable def y : (Litex.R).Carrier := Classical.choose"));
    assert!(generated.contains("Classical.choose_spec"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn existential_elimination_statement_adapters_share_recursive_result_compilation() {
    let generated_from_object_definition = compile_on_verifier_stack(
        "witness exist x R st {x = 1} from 1:\n    1 = 1\nhave selected R:\n    selected = 1\nselected = 1\n",
        "object_by_existential_elimination_adapter.lit",
    )
    .expect("compile the direct object-by-existential Result adapter");
    assert!(
        generated_from_object_definition.contains("noncomputable def selected"),
        "{generated_from_object_definition}"
    );
    assert!(generated_from_object_definition.contains("Classical.choose_spec"));
    assert!(!generated_from_object_definition.contains("sorry"));

    let generated_from_predicate = compile_on_verifier_stack(
        "prop has_copy(a R):\n    exist x R st {x = a}\nwitness exist x R st {x = 2} from 2:\n    2 = 2\nby def $has_copy(2)\nobtain copy from $has_copy(2)\ncopy = 2\n",
        "predicate_backed_existential_elimination_adapter.lit",
    )
    .expect("compile the direct predicate-backed obtain Result adapter");
    assert!(
        generated_from_predicate.contains("noncomputable def copy"),
        "{generated_from_predicate}"
    );
    assert!(generated_from_predicate.contains("unfold has_copy at __definition"));
    assert!(generated_from_predicate.contains("Classical.choose_spec"));
    assert!(!generated_from_predicate.contains("Litex.Object"));
    assert!(!generated_from_predicate.contains("LitexObject"));
    assert!(!generated_from_predicate.contains("sorry"));

    let generated_from_theorem = compile_on_verifier_stack(
        "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}\n    witness exist x R st {x = a} from a:\n        a = a\nobtain theorem_copy from thm self_exists(3)\n",
        "theorem_backed_existential_elimination_adapter.lit",
    )
    .expect("compile the direct theorem-backed obtain Result adapter");
    assert!(
        generated_from_theorem.contains("noncomputable def theorem_copy"),
        "{generated_from_theorem}"
    );
    assert!(generated_from_theorem.contains("self_exists (3 : ℝ)"));
    assert!(generated_from_theorem.contains("Classical.choose_spec"));
    assert!(!generated_from_theorem.contains("Litex.Object"));
    assert!(!generated_from_theorem.contains("LitexObject"));
    assert!(!generated_from_theorem.contains("sorry"));
}

#[test]
fn object_definitions_emit_native_values_and_replay_definition_evidence() {
    let generated = compile_direct_result_only_on_verifier_stack(
        "let x = 1\nx = 1\nhave y R = 1\ny $in R\ny = 1\nthm local_definition:\n    ? forall:\n        2 = 2\n    let z = 2\n    z = 2\n",
        "11_ObjectDefinitions.lit",
    )
    .expect("compile native object-definition tracer");
    assert!(generated.contains("noncomputable def x := (1 : ℂ)"));
    assert!(generated.contains("noncomputable def y := (1 : ℂ)"));
    assert!(generated.contains("Litex.In y Litex.R"));
    assert!(generated.contains("unfold x"));
    assert!(generated.contains("unfold y"));
    assert!(generated.contains("let z := (2 : ℂ)"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn named_real_functions_compile_compound_bodies_and_domain_clauses() {
    let generated = compile_direct_result_only_on_verifier_stack(
        "have fn id(x R) R = x\nid(1) = 1\nhave fn inc(x R) R = x + 1\ninc(1) = 1 + 1\nhave fn reciprocal(x R: x != 0) R = 1 / x\nforall a R:\n    a != 0\n    =>:\n        reciprocal(a) = 1 / a\nhave fn into_builder(x R) {z R: z = z} = x\ninto_builder(1) = 1\n",
        "12_NamedFunction.lit",
    )
    .expect("compile compound named-function tracer");
    assert!(generated.contains("noncomputable def id : Litex.Fn Litex.R Litex.R"));
    assert!(generated.contains("Litex.In id (Litex.fnSet Litex.R Litex.R)"));
    assert!(generated.contains("Litex.fnApplyCarrier (domain := Litex.R) (codomain := Litex.R) id"));
    assert!(generated.contains("Litex.In.rep_exact ((1 : ℝ))"));
    assert!(generated.contains("noncomputable def inc : Litex.Fn Litex.R Litex.R"));
    assert!(generated.contains("Litex.Same.realAddComplex"));
    assert!(generated.contains("noncomputable def reciprocal : Litex.FnWhere"));
    assert!(generated.contains("Litex.fnSetWhere Litex.R Litex.R"));
    assert!(generated.contains("Litex.fnApplyWhereOwn reciprocal"));
    assert!(generated.contains("Litex.Same.realDivComplex"));
    assert!(generated.contains("@Litex.Same _ _ (Litex.ComplexObserver.none _)"));
    assert!(!generated.contains("Litex.Same.symm (Litex.In.same_rep a (__h8_1))"));
    assert!(generated.contains("noncomputable def into_builder : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.setBuilder Litex.R"));
    assert!(generated.contains("Litex.Same.transNoObservation"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn into_builder"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn concrete_predicate_definition_and_by_def_replay_checked_components() {
    let generated = compile_on_verifier_stack(
        "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
        "13_PredicateDefinitions.lit",
    )
    .expect("compile concrete predicate tracer");
    assert!(generated.contains("def is_unit_pair"));
    assert!(generated.contains("(Litex.In x Litex.R) ∧ (Litex.In y Litex.R)"));
    assert!(generated.contains("unfold is_unit_pair"));
    assert!(generated.contains("is_unit_pair (1 : ℝ) (1 : ℝ)"));
    assert!(generated.contains("Litex.In.own Litex.R (1 : ℝ)"));
    assert!(generated.contains("Litex.Same.realComplex ((1 : ℝ))"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn abstract_predicate_and_explicit_trust_emit_only_source_axioms() {
    const SOURCE: &str = "abstract_prop marked(x)\n\ntrust $marked(1)\n\n$marked(1)\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "25_ExplicitSourceAxioms.lit")
            .expect("capture abstract-predicate and explicit-trust statement-result JSON");
    assert!(result_json.contains("DefAbstractPropStmt"), "{result_json}");
    assert_eq!(
        result_json.matches("\"kind\": \"TrustStmt\"").count(),
        1,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "25_ExplicitSourceAxioms.lit")
        .expect("compile exact source-scoped axiom declarations");
    assert_eq!(generated.matches("axiom ").count(), 2, "{generated}");
    assert!(generated.contains("axiom marked"), "{generated}");
    assert!(
        generated.contains("structure __LitexAbstractPredicate_marked")
            && generated.contains("respectsSame :"),
        "{generated}"
    );
    assert!(
        generated.contains("axiom __fact0 : marked.holds (1 : ℂ)"),
        "{generated}"
    );
    assert!(
        generated.contains("theorem __fact1 : marked.holds (1 : ℂ)"),
        "{generated}"
    );
    assert!(generated.contains("exact __fact0"), "{generated}");
    assert!(!generated.contains("sorry"));

    let ordinary = compile_on_verifier_stack("1 = 1\n", "ordinary_no_axiom.lit")
        .expect("compile an ordinary checked statement without an axiom");
    assert_eq!(ordinary.matches("axiom ").count(), 0, "{ordinary}");

    let unproved = compile_on_verifier_stack(
        "abstract_prop unproved(x)\n\n$unproved(1)\n",
        "unproved_abstract_predicate.lit",
    )
    .expect_err("an abstract interface definition must not prove an application");
    assert!(
        unproved.contains("verification failed") || unproved.contains("unknown result"),
        "{unproved}"
    );
}

#[test]
fn set_builder_membership_and_nonempty_choice_use_exact_carriers() {
    let generated = compile_on_verifier_stack(
        "have S set = {x R: x = x}\nS = S\n1 $in {x R: x = 1}\nprop is_one(x R):\n    x = 1\n1 = 1\nby def $is_one(1)\n1 $in {x R: $is_one(x)}\nhave chosen R\nchosen $in R\n",
        "14_SetBuilderAndChoice.lit",
    )
    .expect("compile set-builder and choice tracer");
    assert!(generated.contains("Litex.setBuilder Litex.R"));
    assert!(generated.contains("Litex.Rules.inSetBuilder"));
    assert!(generated.contains("Litex.Rules.inBaseOfInSetBuilder"));
    assert!(generated.contains("Litex.Same.trans (Litex.Same.symm"));
    assert!(generated.contains("rcases Litex.Rules.inSetBuilder_iff.mp"));
    assert!(generated.contains("unfold is_one at __source ⊢"));
    assert!(generated.contains("noncomputable def chosen : Litex.R.Carrier"));
    assert!(generated.contains("Litex.In.own Litex.R chosen"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn set_builder_predicate_transport_is_not_specialized_to_one_argument() {
    let generated = compile_on_verifier_stack(
        "prop anchored_at(anchor R, value R):\n    value = anchor\n1 = 1\nby def $anchored_at(1, 1)\n1 $in {x R: $anchored_at(1, x)}\n",
        "captured_set_builder_predicate.lit",
    )
    .expect("compile a set-builder predicate with a captured argument");

    assert!(generated.contains("def anchored_at"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.inSetBuilder"),
        "{generated}"
    );
    assert!(generated.contains("unfold anchored_at"), "{generated}");
    for forbidden in ["LitexObject", "Litex.Object", "Set.univ", "sorry", "axiom "] {
        assert!(
            !generated.contains(forbidden),
            "forbidden `{forbidden}` in:\n{generated}"
        );
    }
}

#[test]
fn builtin_strategy_result_marks_each_selected_layer_and_replays_exact_rules() {
    const SOURCE: &str = "forall a, b, c, d R:\n    a > 0\n    b >= 0\n    c >= 0\n    d >= 0\n    =>:\n        (a + b) + (c + d) > 0\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture builtin-strategy statement-result JSON");
    assert_eq!(
        result_json.matches("\"kind\": \"BuiltinStrategy\"").count(),
        3,
        "{result_json}"
    );
    assert!(
        result_json.contains("AddPositiveLeftStrict"),
        "{result_json}"
    );
    assert!(
        result_json.contains("\"rule_id\": \"order.add_nonnegative\""),
        "{result_json}"
    );
    assert!(
        result_json.matches("FactCitation").count() >= 4,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile builtin-strategy tracer");
    assert_eq!(
        generated
            .matches("Litex.Rules.complexAddPositiveLeftStrict")
            .count(),
        2
    );
    assert!(generated.contains("Litex.Rules.complexAddNonnegative"));
    assert!(generated.contains("Litex.Rules.realCastPositive (Litex.In.rep a"));
    assert!(generated.contains("Litex.Rules.realCastNonnegative (Litex.In.rep b"));
    assert!(generated
        .contains("Litex.Rules.complexNegativeOneMulNegative (Litex.Rules.realCastPositive"));
    assert!(generated.contains("Litex.Negative.toNonpositive (__infer"));
    assert!(!generated.contains("Litex.Positive.congr"));
    assert!(!generated.contains("Litex.Same.realComplex"));
    assert!(!generated.contains("sorry"));

    const REAL_ADDITION_CARRIER_SOURCE: &str = "forall a, b R:\n    a + b $in R\n";
    let carrier_result_json = capture_statement_results_json_on_verifier_stack(
        REAL_ADDITION_CARRIER_SOURCE,
        "15_BuiltinStrategy.lit",
    )
    .expect("capture real-addition carrier statement-result JSON");
    assert!(
        carrier_result_json.contains("RealArithmeticMembershipClosure"),
        "{carrier_result_json}"
    );
    let carrier_generated =
        compile_on_verifier_stack(REAL_ADDITION_CARRIER_SOURCE, "15_BuiltinStrategy.lit")
            .expect("compile real-addition carrier tracer");
    assert!(carrier_generated.contains("Litex.Rules.complexAddInR"));
    assert!(carrier_generated.contains("Litex.Rules.complexRealInR ((Litex.In.rep a"));
    assert!(carrier_generated.contains("Litex.Rules.complexRealInR ((Litex.In.rep b"));

    const RIGHT_STRICT_SOURCE: &str = "forall a, b, c, d R:\n    a >= 0\n    b >= 0\n    c >= 0\n    d > 0\n    =>:\n        (a + b) + (c + d) > 0\n";
    let right_result_json = capture_statement_results_json_on_verifier_stack(
        RIGHT_STRICT_SOURCE,
        "15_BuiltinStrategy.lit",
    )
    .expect("capture right-strict builtin-strategy statement-result JSON");
    assert!(
        right_result_json.contains("AddPositiveRightStrict"),
        "{right_result_json}"
    );
    assert!(
        right_result_json.contains("\"rule_id\": \"order.add_positive_of_nonnegative_positive\""),
        "{right_result_json}"
    );

    let right_generated = compile_on_verifier_stack(RIGHT_STRICT_SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile right-strict builtin-strategy tracer");
    assert_eq!(
        right_generated
            .matches("Litex.Rules.complexAddPositiveRightStrict")
            .count(),
        2
    );
    assert!(!right_generated.contains("Litex.Object"));
    assert!(!right_generated.contains("Set.univ"));
    assert!(!right_generated.contains("axiom "));
    assert!(!right_generated.contains("sorry"));
}

#[test]
fn real_arithmetic_membership_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b R:\n    a + b $in R\n\nforall a, b R:\n    a - b $in R\n\nforall a, b R:\n    a * b $in R\n\nforall a, b R:\n    b != 0\n    =>:\n        a / b $in R\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture real arithmetic closure statement-result JSON");
    assert!(
        result_json
            .matches("RealArithmeticMembershipClosure")
            .count()
            >= 4,
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile real arithmetic closure tracer");
    for theorem in [
        "Litex.Rules.complexAddInR",
        "Litex.Rules.complexSubInR",
        "Litex.Rules.complexMulInR",
        "Litex.Rules.complexDivInR",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multiplicative_strategy_replays_canonical_mathlib_order_evidence() {
    const SOURCE: &str = "forall a, b, c, d R:\n    a >= 0\n    b >= 0\n    c >= 0\n    d >= 0\n    =>:\n        (a * b) * (c * d) >= 0\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture nested multiplicative strategy statement-result JSON");
    assert!(result_json.contains("BuiltinStrategy"), "{result_json}");
    assert!(result_json.contains("MulNonnegative"), "{result_json}");

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile nested multiplicative signs through canonical zero order");
    assert_eq!(
        generated
            .matches("Litex.Rules.complexMulNonnegative")
            .count(),
        3,
        "{generated}"
    );
    assert!(generated.contains("Litex.Nonnegative"));
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn direct_multiplicative_and_divisive_sign_rules_all_compile() {
    const SOURCE: &str = "forall a, b R:\n    a >= 0\n    b >= 0\n    =>:\n        a * b >= 0\n\nforall a, b R:\n    a > 0\n    b > 0\n    =>:\n        a * b > 0\n\nforall a, b R:\n    a >= 0\n    b > 0\n    =>:\n        a / b >= 0\n\nforall a, b R:\n    a > 0\n    b > 0\n    =>:\n        a / b > 0\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture direct multiplication/division sign statement-result JSON");
    for rule in [
        "MulNonnegative",
        "MulPositive",
        "DivNonnegative",
        "DivPositive",
    ] {
        assert!(result_json.contains(rule), "missing {rule}: {result_json}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile direct multiplication/division sign rules");
    for theorem in [
        "Litex.Rules.complexMulNonnegative",
        "Litex.Rules.complexMulPositive",
        "Litex.Rules.complexDivNonnegative",
        "Litex.Rules.complexDivPositive",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn subtractive_strategy_rule_compiles_from_registered_certificate() {
    const SOURCE: &str = "forall a, b R:\n    a <= b\n    =>:\n        b - a >= 0\n";
    let result_json = capture_statement_results_json_on_verifier_stack(
        SOURCE,
        "subtractive_builtin_strategy_rule.lit",
    )
    .expect("capture the registered subtractive-sign certificate");
    assert!(result_json.contains("SubNonnegativeFromLessEqual"));

    let generated = compile_on_verifier_stack(SOURCE, "subtractive_builtin_strategy_rule.lit")
        .expect("compile the reviewed subtractive-sign rule");
    assert!(generated.contains("Litex.Rules.complexSubNonnegativeOfLessEqual"));
    assert!(generated.contains("(u := (Litex.In.rep b"));
    assert!(generated.contains("(v := (Litex.In.rep a"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn nested_set_builder_binder_expression_remains_fail_closed() {
    let error = compile_on_verifier_stack(
        "2 $in {x R: x + 1 = 3}\n",
        "unsupported_nested_set_builder_transport.lit",
    )
    .expect_err("nested predicate transport must remain outside the reviewed adapter");
    assert!(
        error.contains("whole equality side") || error.contains("set-builder"),
        "unexpected error: {error}"
    );
}

#[test]
fn multi_parameter_named_function_uses_the_same_telescope_contract() {
    let generated = compile_on_verifier_stack(
        "have fn first(x, y R) R = x\nfirst(1, 1) = 1\n",
        "multi_parameter_function.lit",
    )
    .expect("compile a named two-parameter telescope function");
    assert!(generated.contains("noncomputable def first : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.fnTelescopeSet"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn first"));
    assert!(generated.contains("ULift.up"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn indexed_tuple_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str = include_str!("../../lean/examples/29_IndexedTupleCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "29_IndexedTupleCompilerEnvironment.lit")
        .expect("compile indexed tuple from its recursive statement Result");
    assert!(generated.contains("noncomputable def coordinates : Litex.IndexedTuple 3 ℂ"));
    assert!(generated.contains("fun __index"));
    assert!(generated.contains("Litex.IsTuple coordinates"));
    assert!(generated.contains("Litex.tupleDim coordinates"));
    assert!(generated.contains("Litex.indexedTupleAt coordinates"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn indexed_sequence_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str =
        include_str!("../../lean/examples/30_IndexedSequenceCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "30_IndexedSequenceCompilerEnvironment.lit")
        .expect("compile indexed sequence from its recursive statement Result");
    assert!(generated.contains("noncomputable def shifted_sequence : Litex.Fn Litex.NPos Litex.R"));
    assert!(generated.contains("Litex.sequenceSet Litex.R"));
    assert!(generated.contains("Litex.fnSet Litex.NPos Litex.R"));
    assert!(generated.contains("Litex.In.rep __arg __arg_in"));
    assert!(generated.contains("Litex.fnApplyCarrier (domain := Litex.NPos)"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn template_sequence_alias_compiles_from_recursive_results_without_index_shift() {
    const SOURCE: &str =
        include_str!("../../lean/examples/55_TemplateSequenceInstantiationResult.lit");
    let result_json = capture_statement_results_json_on_verifier_stack(
        SOURCE,
        "55_TemplateSequenceInstantiationResult.lit",
    )
    .expect("capture Template definition and Created/object-WD-Reuse statement-result JSON");
    for retained_field in [
        "\"template_parameter_groups\"",
        "\"body_statement_result\"",
        "\"kind\": \"Created\"",
        "\"kind\": \"Reuse\"",
        "\"template_argument_results\"",
        "\"public_value_equalities\"",
    ] {
        assert!(
            result_json.contains(retained_field),
            "missing {retained_field}: {result_json}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "55_TemplateSequenceInstantiationResult.lit")
        .expect("compile Template sequence alias directly from recursive statement Results");
    assert!(
        generated.contains(
            "abbrev sequence (S : Litex.Set) := (Litex.fnSet Litex.NPos (S : Litex.Set.{0}))"
        ),
        "{generated}"
    );
    assert!(
        generated.contains(
            "@Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) (sequence Litex.R) (Litex.fnSet Litex.NPos Litex.R)",
        ),
        "{generated}"
    );
    assert!(!generated.contains("Nat ->"), "{generated}");
    assert!(!generated.contains("+ 1"), "{generated}");
    assert!(!generated.contains("- 1"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
    assert_eq!(
        generated,
        include_str!("../../lean/examples/55_TemplateSequenceInstantiationResult.lean"),
        "the checked-in Template tracer must not drift from direct Result compilation"
    );
}

#[test]
fn unsupported_template_compiler_shapes_remain_fail_closed() {
    for (label, source, expected_error) in [
        (
            "template_domain_is_not_yet_compiled.lit",
            "template<S set: S = S>:\n    have guarded set = S\n\n\\guarded<R> = R\n",
            "no template domain clauses",
        ),
        (
            "template_non_set_parameter_is_not_yet_compiled.lit",
            "template<n N+>:\n    have naturals set = N\n\n\\naturals<1> = N\n",
            "only one or more `set` parameters",
        ),
        (
            "template_non_set_alias_body_is_not_yet_compiled.lit",
            "template<S set>:\n    have fn identity(x S) S = x\n",
            "only a `have <name> set = <value>` body",
        ),
    ] {
        let error = compile_on_verifier_stack(source, label)
            .expect_err("unsupported Template shape must remain outside the direct compiler slice");
        assert!(
            error.contains(expected_error),
            "unexpected error for {label}: {error}"
        );
    }
}

#[test]
fn finite_sequence_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str =
        include_str!("../../lean/examples/31_FiniteSequenceCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "31_FiniteSequenceCompilerEnvironment.lit")
        .expect("compile finite sequence from its recursive statement Result");
    assert!(generated.contains("noncomputable def bounded_sequence : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.finiteSequenceSet.{0} Litex.R (3 : Nat)"));
    assert!(generated.contains("Litex.FnTelescope.requirement"));
    assert!(generated.contains("fun __arg_domain => ULift.up"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn bounded_sequence"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn matrix_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str = include_str!("../../lean/examples/32_MatrixCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "32_MatrixCompilerEnvironment.lit")
        .expect("compile matrix from its recursive statement Result");
    assert!(generated.contains("noncomputable def entry_matrix : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.matrixSet.{0} Litex.R (2 : Nat) (3 : Nat)"));
    assert!(generated.contains("Litex.positiveNaturalParameterLessEqualNaturalBound __arg1"));
    assert!(generated.contains("Litex.positiveNaturalParameterLessEqualNaturalBound __arg2"));
    assert!(generated.contains("fun __arg_domain => ULift.up"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn (signature :="));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multiple_existential_witnesses_fail_closed() {
    let error = compile_on_verifier_stack(
        "witness exist x, y R st {x = y} from 1, 1:\n    1 = 1\n",
        "unsupported_multi_witness.lit",
    )
    .expect_err("multiple witnesses must remain outside the reviewed compiler slice");
    assert!(
        error.contains("one positive witness and one body fact")
            || error.contains("one membership witness"),
        "unexpected error: {error}"
    );
}

#[test]
fn collections_and_aggregates_use_exact_typed_carriers() {
    const SOURCE: &str = include_str!("../../lean/examples/26_CollectionsAndAggregates.lit");
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "26_CollectionsAndAggregates.lit")
            .expect("capture collection and aggregate statement-result JSON");
    for evidence in ["\"kind\": \"FiniteSet\"", "ListSetMembership"] {
        assert!(
            result_json.contains(evidence),
            "missing collection evidence {evidence}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "26_CollectionsAndAggregates.lit")
        .expect("compile typed collection and aggregate tracer");
    for term in [
        "Litex.Set.coproduct",
        "Litex.SingletonCarrier.element",
        "Litex.generalCart",
        "Litex.FnTelescope.Carrier",
        "Litex.closedRange",
        "Litex.SequenceLiteral.mk",
    ] {
        assert!(
            generated.contains(term),
            "missing generated collection term {term}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn set_operators_replay_catalog_certificates_and_reject_non_catalog_rules() {
    const SOURCE: &str = include_str!("../../lean/examples/27_SetOperators.lit");
    const LEFT_BOUNDARY: &str =
        "forall A, B, D set, x D:\n    not x $in A\n    =>:\n        not x $in intersect(A, B)\n";
    const RIGHT_BOUNDARY: &str =
        "forall A, B, D set, x D:\n    not x $in B\n    =>:\n        not x $in intersect(A, B)\n";
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "27_SetOperators.lit")
            .expect("capture set-operator statement-result JSON");
    for rule in [
        "set.union_commutative",
        "set.union_associative",
        "set.intersect_commutative",
        "set.intersect_associative",
        "set.set_minus_membership",
    ] {
        assert!(result_json.contains(rule), "missing {rule}: {result_json}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "27_SetOperators.lit")
        .expect("compile exact catalog set operators");
    for theorem in [
        "Litex.SetRules.unionCommutative",
        "Litex.SetRules.unionAssociative",
        "Litex.SetRules.intersectCommutative",
        "Litex.SetRules.intersectAssociative",
        "Litex.SetRules.inSetMinus",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    for (source, rule_id) in [
        (LEFT_BOUNDARY, "set.intersect_nonmembership_left"),
        (RIGHT_BOUNDARY, "set.intersect_nonmembership_right"),
    ] {
        let boundary_json =
            capture_statement_results_json_on_verifier_stack(source, "27_SetOperatorsBoundary.lit")
                .expect("non-catalog intersection nonmembership verifies with typed evidence");
        assert!(
            boundary_json.contains(&format!("\"rule_id\": \"{rule_id}\"")),
            "{boundary_json}"
        );

        let boundary = compile_on_verifier_stack(source, "27_SetOperatorsBoundary.lit")
            .expect_err("non-catalog intersection nonmembership must fail closed");
        assert!(boundary.contains(rule_id), "{boundary}");
    }
}

#[test]
fn extended_set_rules_use_exact_power_set_and_subset_certificates() {
    const SOURCE: &str = include_str!("../../lean/examples/28_ExtendedSetRules.lit");
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "28_ExtendedSetRules.lit")
            .expect("capture extended set-rule certificates");
    for rule in [
        "set.empty_subset",
        "set.union_finite",
        "set.intersect_finite",
        "set.power_set_membership_of_subset",
        "set.power_set_finite",
        "set.set_minus_union_de_morgan",
    ] {
        assert!(
            result_json.contains(rule),
            "missing registered certificate {rule}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "28_ExtendedSetRules.lit")
        .expect("compile extended exact-carrier set rules");
    for theorem in [
        "Litex.SetRules.emptySubset",
        "Litex.SetRules.unionFinite",
        "Litex.SetRules.intersectFinite",
        "Litex.SetRules.inPowerSetOfSubset",
        "Litex.SetRules.powerSetFinite",
        "Litex.SetRules.setMinusUnionDeMorgan",
    ] {
        assert!(
            generated.contains(theorem),
            "missing generated theorem {theorem}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn elementary_set_algebra_completion_replays_exact_certificates() {
    const SOURCE: &str = include_str!("../../lean/examples/58_ElementarySetAlgebraCompletion.lit");
    const BOUNDARY_SOURCE: &str =
        "forall A, B, D set:\n    A $subset B\n    B $subset D\n    =>:\n        A $subset D\n";
    let result_json = capture_statement_results_json_on_verifier_stack(
        SOURCE,
        "58_ElementarySetAlgebraCompletion.lit",
    )
    .expect("capture elementary set-algebra certificates");
    for rule in [
        "set.union_set_minus_decomposition",
        "set.intersect_set_minus_self_empty",
        "set.intersect_idempotent",
        "set.set_minus_self_empty",
        "set.union_eq_right_of_subset",
    ] {
        assert!(result_json.contains(rule), "missing set certificate {rule}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "58_ElementarySetAlgebraCompletion.lit")
        .expect("compile catalog elementary set-algebra certificates");
    for theorem in [
        "Litex.SetRules.unionSetMinusDecomposition",
        "Litex.SetRules.intersectSetMinusSelfEmpty",
        "Litex.SetRules.intersectIdempotent",
        "Litex.SetRules.setMinusSelfEmpty",
        "Litex.SetRules.unionEqRightOfSubset",
        "Litex.SetRules.intersectSetMinusOfSubsetEmpty",
    ] {
        assert!(
            generated.contains(theorem),
            "missing generated theorem {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary_json = capture_statement_results_json_on_verifier_stack(
        BOUNDARY_SOURCE,
        "58_ElementarySetAlgebraCompletionBoundary.lit",
    )
    .expect("capture typed subset-transitivity boundary");
    assert!(boundary_json.contains("\"rule_id\": \"set.subset_transitivity\""));

    let boundary = compile_on_verifier_stack(
        BOUNDARY_SOURCE,
        "58_ElementarySetAlgebraCompletionBoundary.lit",
    )
    .expect_err("non-catalog subset transitivity must fail closed");
    assert!(boundary.contains("set.subset_transitivity"), "{boundary}");
}

#[test]
fn transparent_let_resolution_replays_exact_definition_certificate() {
    const SOURCE: &str = include_str!("../../lean/examples/59_TransparentLetResolution.lit");
    let result_json =
        capture_statement_results_json_on_verifier_stack(SOURCE, "59_TransparentLetResolution.lit")
            .expect("capture transparent let definition certificate");
    assert!(
        result_json.contains(r#""kind": "TransparentDefinitionReduction""#),
        "{result_json}"
    );
    assert!(
        result_json.contains(r#""defining_equality_fact_id": "f7""#),
        "{result_json}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "59_TransparentLetResolution.lit")
        .expect("compile transparent let definition certificate");
    assert!(
        generated.contains("noncomputable def g := f"),
        "{generated}"
    );
    assert!(
        generated.contains("(by\n  unfold g\n  exact"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}
