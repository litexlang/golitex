use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::prelude::*;

const MEMBERSHIP: &str =
    include_str!("../../../lean/examples/coordinate_pair_membership/statement.lit");
const FIELDS: &str = include_str!("../../../lean/examples/coordinate_pair_fields/statement.lit");

fn declaration(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::ExecDefStructStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        crate::execute::ExecDefStructStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("struct declaration")
    };
    p
}

#[test]
fn struct_examples_replay_exact_results() {
    for source in [
        MEMBERSHIP,
        FIELDS,
        include_str!("../../../lean/examples/indexed_point_fields/statement.lit"),
        include_str!("../../../lean/examples/arbitrary_carrier_pairs/statement.lit"),
        include_str!("../../../lean/examples/nested_coordinate_membership/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "structures")
            .unwrap_or_else(|error| panic!("{}: {error:?}", source.lines().next().unwrap()));
        assert_eq!(lean, compiler.compile_run(&run, "structures").unwrap());
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn struct_fields_require_ordered_wd_and_distinct_binders() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(MEMBERSHIP);
        let p = declaration(&mut run);
        match change {
            0 => {
                p.field_scope.fields.pop();
            }
            1 => super::replace_wd_subject(
                &mut p.field_scope.fields[0].well_defined,
                Obj::StandardSet(StandardSet::Z),
            ),
            2 => p.statement.fields[1].binding.id = p.statement.fields[0].binding.id,
            3 => p.field_scope.fields.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "changed_field").is_err());
    }
}

#[test]
fn struct_membership_checks_each_original_coordinate() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(MEMBERSHIP);
        let p = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::StructObjMembership(proof),
            ),
        ) = &mut p.searched_proof
        else {
            panic!("original structure membership")
        };
        match change {
            0 => {
                proof.carrier_obligations.pop();
            }
            1 => proof.carrier_obligations.swap(0, 1),
            2 => {
                let child = proof.carrier_obligations.pop().unwrap();
                proof.equivalent_fact_proofs.push(child);
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "changed_membership").is_err());
    }
}

#[test]
fn struct_calls_need_the_original_visible_declaration() {
    for future in [false, true] {
        let (mut run, compiler) = super::execute(MEMBERSHIP);
        if future {
            run.statement_results.swap(0, 1);
        } else {
            run.statement_results.remove(0);
        }
        assert!(compiler.compile_run(&run, "missing_struct").is_err());
    }
}

#[test]
fn struct_parameters_preserve_their_auto_open_capture() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(FIELDS);
        let p = super::forall_proof_mut(&mut run.statement_results[1]);
        let layers = &mut p.introduced_params.auto_opened_struct_layers;
        match change {
            0 => *layers = None,
            1 => layers.as_mut().unwrap().clear(),
            2 => layers.as_mut().unwrap()[0].obj = Obj::StandardSet(StandardSet::R),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "changed_layer").is_err());
    }
}

#[test]
fn struct_release_checks_all_ordered_stores() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(FIELDS);
        let layer = &mut super::forall_proof_mut(&mut run.statement_results[1])
            .introduced_params
            .auto_opened_struct_layers
            .as_mut()
            .unwrap()[0];
        match change {
            0 => {
                layer.store_and_infer.pop();
            }
            1 => layer.store_and_infer.swap(1, 2),
            2 => layer.store_and_infer.swap(3, 4),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "changed_stores").is_err());
    }
}

#[test]
fn struct_dependencies_and_local_scope_are_not_discarded() {
    for source in ["sketch:\n    struct LocalPair:\n        x R\n        y R\n"] {
        let (run, compiler) = super::execute(source);
        assert!(compiler.compile_run(&run, "unsupported_structure").is_err());
    }
}

#[test]
fn quantified_struct_laws_replay_fields_domains_and_publications() {
    for source in [
        include_str!("../../../lean/examples/struct_universal_function_law/statement.lit"),
        include_str!("../../../lean/examples/struct_dependent_universal_law/statement.lit"),
        include_str!("../../../lean/examples/struct_guarded_universal_law/statement.lit"),
        include_str!("../../../lean/examples/struct_generic_universal_law/statement.lit"),
        "struct ConstantLawPair:\n    x R\n    y R\n    <=>:\n        forall z R:\n            z = z\n",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "universal_struct").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "universal_struct").unwrap());
    }
}

#[test]
fn quantified_struct_laws_retain_formation_and_flattened_publication() {
    let source = include_str!("../../../lean/examples/struct_guarded_universal_law/statement.lit");
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(source);
        let p = declaration(&mut run);
        match mutation {
            0 => p.field_scope.equivalent_facts.clear(),
            1 => {
                let FactWellDefinedProof::ForallFact(wd) =
                    &mut p.field_scope.equivalent_facts[0].well_defined
                else {
                    panic!("universal formation")
                };
                wd.as_detailed_mut().unwrap().then.clear();
            }
            2 => p.definition_facts[0].source_fact_id = FactId::new(u64::MAX),
            _ => {
                let StoreFactResult::ForallFact(stored) =
                    &mut p.definition_facts[0].store_and_infer.store
                else {
                    panic!("published universal")
                };
                match mutation {
                    3 => {
                        stored.fact.typed_parameters.groups.pop();
                    }
                    4 => {
                        stored.fact.dom_facts.remove(0);
                    }
                    5 => {
                        stored.fact.dom_facts.pop();
                    }
                    6 => stored.fact.then_facts.clear(),
                    7 => {
                        stored
                            .fact
                            .typed_parameters
                            .groups
                            .last_mut()
                            .unwrap()
                            .param_type = ParamType::Obj(Obj::StandardSet(StandardSet::Z));
                    }
                    _ => unreachable!(),
                }
            }
        }
        compiler
            .compile_run(&run, "changed_universal_struct")
            .expect_err(
                "original law formation, binders, guard, type facts and conclusion must remain",
            );
    }
}

#[test]
fn quantified_struct_laws_keep_private_scope_and_invalid_call_boundaries() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let source = include_str!("../../../lean/examples/struct_guarded_universal_law/statement.lit");
    let (run, compiler) = super::execute(source);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        crate::execute::ExecDefStructStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!("struct declaration")
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let condition = &p.field_scope.equivalent_facts[0];
    assert!(outside
        .visible_fact(condition.store.primary_fact_id(), &compiler.runtime)
        .is_err());
    assert!(outside
        .visible_fact(
            p.definition_facts[0].store_and_infer.primary_fact_id(),
            &compiler.runtime
        )
        .is_ok());
    let invalid =
        format!("{source}\nforall p &GuardedInverseFunctionPair:\n    p.reciprocal(0) $in R\n");
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(&invalid).unwrap();
    assert!(!run.success);
    crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_guarded_record")
        .expect_err("the field's nonzero guard still applies");
}

#[test]
fn struct_membership_cannot_ignore_a_field_domain() {
    let source = "struct IndexedPoint:\n    coordinate R\n    index N\n(1, -1) $in &IndexedPoint\n";
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_member")
        .is_err());
}

#[test]
fn struct_release_does_not_cite_its_future_stores() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(FIELDS);
    let proof = super::forall_proof_mut(&mut run.statement_results[1]);
    let header = SourcePosition::new(None, SourceOwner::Forall(proof), 1);
    let layer = &proof
        .introduced_params
        .auto_opened_struct_layers
        .as_ref()
        .unwrap()[0];
    for (index, store) in layer.store_and_infer.iter().enumerate() {
        let prior = SourcePosition::new(Some(&header), SourceOwner::StructLayer(layer), index);
        assert!(prior
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_err());
        let completed = SourcePosition {
            before: index + 1,
            ..prior
        };
        assert!(completed
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_ok());
    }
}

#[test]
fn struct_non_numeric_fields_are_not_rational_scalar_leaves() {
    let source = "struct SetPair:\n    first {R}\n    second {C}\nforall p &SetPair:\n    p.first = p.first\n";
    let (mut run, compiler) = super::execute(source);
    let equality = super::equality_proof_mut(
        &mut super::forall_proof_mut(&mut run.statement_results[1]).proved_then_facts[0]
            .verify_result,
    );
    equality.searched_proof =
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {},
        ));
    assert!(compiler.compile_run(&run, "non_numeric_field").is_err());
}

const CHOSEN: &str = include_str!("../../../lean/examples/chosen_coordinate_fields/statement.lit");
const ORIGIN: &str = include_str!("../../../lean/examples/origin_coordinate_fields/statement.lit");
const RELEASED: &str =
    include_str!("../../../lean/examples/released_coordinate_fields/statement.lit");
const TWO_PAIRS: &str =
    include_str!("../../../lean/examples/coordinate_pair_addition/statement.lit");

#[test]
fn struct_binding_examples_replay_results_in_global_and_local_scopes() {
    for source in [
        CHOSEN,
        ORIGIN,
        RELEASED,
        TWO_PAIRS,
        include_str!("../../../lean/examples/local_coordinate_objects/statement.lit"),
        include_str!("../../../lean/examples/coordinate_field_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "bindings")
            .unwrap_or_else(|e| panic!("{}: {e:?}", source.lines().next().unwrap()));
        assert_eq!(lean, compiler.compile_run(&run, "bindings").unwrap());
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn struct_have_requires_all_original_layers_in_parameter_order() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(CHOSEN);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) = &mut run.statement_results[2]
        else {
            panic!("have");
        };
        match change {
            0 => p.auto_opened_struct_layers = None,
            1 => {
                p.auto_opened_struct_layers.as_mut().unwrap().pop();
            }
            2 => p.auto_opened_struct_layers.as_mut().unwrap().swap(0, 1),
            3 => p.auto_opened_struct_layers.as_mut().unwrap()[0]
                .store_and_infer
                .swap(1, 2),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "broken_have").is_err());
    }
}

#[test]
fn struct_typed_alias_checks_preflight_and_actual_layers_separately() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(ORIGIN);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) = &mut run.statement_results[1]
        else {
            panic!("alias");
        };
        match change {
            0 => p.type_preflight.auto_opened_struct_layers = None,
            1 => p.auto_opened_struct_layers = None,
            2 => p.type_preflight.auto_opened_struct_layers.as_mut().unwrap()[0]
                .store_and_infer
                .swap(1, 2),
            3 => {
                p.auto_opened_struct_layers.as_mut().unwrap()[0].obj =
                    Obj::StandardSet(StandardSet::R)
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "broken_alias").is_err());
    }
}

#[test]
fn struct_explicit_release_checks_subject_carrier_and_order() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(RELEASED);
        let ExecStmtResult::ReleaseAndExpand(
            crate::execute::ExecReleaseAndExpandStmtResult::StructDef(
                crate::execute::ExecReleaseStructDefStmtResult::Success(p),
            ),
        ) = &mut run.statement_results[3]
        else {
            panic!("release");
        };
        match change {
            0 => p.release.obj = Obj::StandardSet(StandardSet::R),
            1 => {
                p.release.store_and_infer.pop();
            }
            2 => p.release.store_and_infer.swap(3, 4),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "broken_release").is_err());
    }
}

#[test]
fn struct_auto_open_cannot_cite_later_parameter_layers() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(TWO_PAIRS);
    let p = super::forall_proof_mut(&mut run.statement_results[1]);
    let header = SourcePosition::new(None, SourceOwner::Forall(p), 2);
    let layers = p
        .introduced_params
        .auto_opened_struct_layers
        .as_deref()
        .unwrap();
    let first = SourcePosition::new(Some(&header), SourceOwner::StructLayers(layers), 1);
    let second = SourcePosition { before: 2, ..first };
    for store in &layers[1].store_and_infer {
        assert!(first
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_err());
        assert!(second
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_ok());
    }
    let field = Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
        obj: Box::new(layers[1].obj.clone()),
        fields: vec!["x".into()],
    }));
    assert!(first
        .with_visible_inferred_subject_filter(&field, &mut |_, _| Ok(Some(())))
        .unwrap()
        .is_none());
    assert!(second
        .with_visible_inferred_subject_filter(&field, &mut |_, _| Ok(Some(())))
        .unwrap()
        .is_some());
}

#[test]
fn struct_explicit_release_cannot_cite_its_own_result_before_membership() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(RELEASED);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 3);
    let prior = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[3]),
        0,
    );
    let ExecStmtResult::ReleaseAndExpand(
        crate::execute::ExecReleaseAndExpandStmtResult::StructDef(
            crate::execute::ExecReleaseStructDefStmtResult::Success(p),
        ),
    ) = &run.statement_results[3]
    else {
        panic!("release");
    };
    for store in &p.release.store_and_infer {
        assert!(prior
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_err());
    }
}

#[test]
fn struct_declaration_layers_follow_parameter_and_alias_formation() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    for (source, index) in [(CHOSEN, 2), (ORIGIN, 1)] {
        let (run, compiler) = super::execute(source);
        let (stage, layers) = match &run.statement_results[index] {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjInNonemptySet(
                    ExecHaveObjInNonemptySetStmtResult::Success(p),
                ),
            )) => (2, p.auto_opened_struct_layers.as_ref().unwrap()),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
            )) => (3, p.auto_opened_struct_layers.as_ref().unwrap()),
            _ => panic!("declaration"),
        };
        let root = SourcePosition::new(None, SourceOwner::Run(&run), index);
        let before = SourcePosition::new(
            Some(&root),
            SourceOwner::Statement(&run.statement_results[index]),
            stage,
        );
        for layer in layers {
            for store in &layer.store_and_infer {
                assert!(before
                    .visible_fact(store.primary_fact_id(), &compiler.runtime)
                    .is_err());
            }
        }
    }
}

const POSITIVE_POINT: &str =
    include_str!("../../../lean/examples/positive_point_conditions/statement.lit");
const POSITIVE_RATIO: &str =
    include_str!("../../../lean/examples/positive_ratio_conditions/statement.lit");

#[test]
fn constrained_struct_examples_replay_original_conditions() {
    for source in [
        POSITIVE_POINT,
        POSITIVE_RATIO,
        include_str!("../../../lean/examples/positive_point_release/statement.lit"),
        include_str!("../../../lean/examples/ordered_coordinate_conditions/statement.lit"),
        include_str!("../../../lean/examples/first_quadrant_conditions/statement.lit"),
        include_str!("../../../lean/examples/chosen_positive_points/statement.lit"),
        include_str!("../../../lean/examples/equal_coordinate_conditions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "constrained_structs")
            .unwrap_or_else(|e| panic!("{}: {e:?}", source.lines().next().unwrap()));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "constrained_structs").unwrap()
        );
        assert!(lean.contains("Litex.setBuilder") && lean.contains("Litex.inSetBuilder_iff"));
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn constrained_struct_conditions_cannot_be_dropped_or_reordered() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(POSITIVE_RATIO);
        let p = declaration(&mut run);
        match change {
            0 => p.field_scope.equivalent_facts.clear(),
            1 => p.field_scope.equivalent_facts.swap(0, 1),
            2 => p.definition_facts.clear(),
            3 => p.definition_facts.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_conditions").is_err());
    }
}

#[test]
fn constrained_struct_membership_requires_each_checked_law() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(POSITIVE_RATIO);
        let p = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::StructObjMembership(proof),
            ),
        ) = &mut p.searched_proof
        else {
            panic!("membership");
        };
        match change {
            0 => {
                proof.equivalent_fact_proofs.pop();
            }
            1 => proof.equivalent_fact_proofs.swap(0, 1),
            2 => proof.carrier_obligations.clear(),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_membership").is_err());
    }
}

#[test]
fn constrained_struct_release_cannot_omit_or_exchange_laws() {
    for change in 0..2 {
        let (mut run, compiler) = super::execute(POSITIVE_RATIO);
        let layer = &mut super::forall_proof_mut(&mut run.statement_results[2])
            .introduced_params
            .auto_opened_struct_layers
            .as_mut()
            .unwrap()[0];
        match change {
            0 => {
                layer.store_and_infer.pop();
            }
            1 => layer.store_and_infer.swap(5, 6),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_release").is_err());
    }
}

#[test]
fn constrained_struct_condition_scope_rejects_future_and_escaped_assumptions() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(POSITIVE_RATIO);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        crate::execute::ExecDefStructStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!("structure");
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    for (index, condition) in p.field_scope.equivalent_facts.iter().enumerate() {
        let prior = SourcePosition::new(
            Some(&root),
            SourceOwner::StructFields(p),
            p.statement.fields.len() + index,
        );
        let completed = SourcePosition {
            before: prior.before + 1,
            ..prior
        };
        let id = condition.store.primary_fact_id();
        assert!(prior.visible_fact(id, &compiler.runtime).is_err());
        assert!(completed.visible_fact(id, &compiler.runtime).is_ok());
        let outside = SourcePosition {
            before: run.statement_results.len(),
            ..root
        };
        assert!(outside.visible_fact(id, &compiler.runtime).is_err());
    }
}

#[test]
fn constrained_struct_publications_retain_the_actual_quantified_shape() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(POSITIVE_POINT);
        let p = declaration(&mut run);
        let StoreFactResult::ForallFact(stored) = &mut p.definition_facts[0].store_and_infer.store
        else {
            panic!("law");
        };
        match change {
            0 => stored.fact.dom_facts.clear(),
            1 => stored.fact.then_facts.clear(),
            2 => stored.fact.typed_parameters.groups.clear(),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_publication").is_err());
    }
}

#[test]
fn constrained_struct_invalid_point_is_rejected_before_compilation() {
    let source = "struct PositivePoint:\n    x R\n    y R\n    <=>:\n        x > 0\n(0, 3) $in &PositivePoint\n";
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_positive_point")
        .is_err());
}

const PARAMETERIZED_PAIR: &str =
    include_str!("../../../lean/examples/parameterized_pairs/statement.lit");
const DESIGNATED_PAIR: &str =
    include_str!("../../../lean/examples/designated_coordinate_pairs/statement.lit");

const NONEMPTY_PAIR: &str =
    include_str!("../../../lean/examples/nonempty_parameterized_pairs/statement.lit");

#[test]
fn nonempty_struct_headers_preserve_kind_facts() {
    for source in [
        NONEMPTY_PAIR,
        include_str!("../../../lean/examples/nonempty_equal_pairs/statement.lit"),
        include_str!("../../../lean/examples/nonempty_cartesian_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "nonempty_headers")
            .unwrap_or_else(|error| panic!("{}: {error:?}", source.lines().next().unwrap()));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "nonempty_headers").unwrap()
        );
        assert!(lean.contains("Litex.IsNonempty _value_i"));
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn nonempty_struct_headers_reject_wrong_kind_and_missing_capture() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(NONEMPTY_PAIR);
        let p = declaration(&mut run);
        match change {
            0 => {
                p.introduced_params
                    .as_mut()
                    .unwrap()
                    .param_type_well_defined[0] = ParamTypeWellDefinedProof::Set
            }
            1 => {
                p.statement.param_def_with_dom.as_mut().unwrap().0.groups[0].param_type =
                    ParamType::Set(Set {})
            }
            2 => p
                .introduced_params
                .as_mut()
                .unwrap()
                .defined_params
                .store_and_infer_results
                .clear(),
            3 => {
                std::rc::Rc::get_mut(
                    &mut p
                        .introduced_params
                        .as_mut()
                        .unwrap()
                        .defined_params
                        .store_and_infer_results[0],
                )
                .unwrap()
                .infer = None
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_nonempty_kind").is_err());
    }
}

#[test]
fn nonempty_structure_arguments_cannot_drop_their_nonempty_proof() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
    let (mut run, compiler) = super::execute(NONEMPTY_PAIR);
    let atomic = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(p)),
        ..
    } = (&mut atomic
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[1])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("struct WD")
    };
    p.requirement_fact_verified.clear();
    assert!(compiler
        .compile_run(&run, "missing_nonempty_proof")
        .is_err());
}

#[test]
fn nonempty_structure_arguments_reject_sethood_and_wrong_subjects() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
    for wrong in ["$is_set(R)", "$is_nonempty_set(C)"] {
        let (mut replacement, _) = super::execute(wrong);
        let (mut run, compiler) = super::execute(NONEMPTY_PAIR);
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(p)),
            ..
        } = (&mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[1])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("struct WD")
        };
        std::mem::swap(
            &mut p.requirement_fact_verified[0],
            &mut super::fact_statement_mut(&mut replacement.statement_results[0]).verify_result,
        );
        assert!(compiler.compile_run(&run, "wrong_nonempty_proof").is_err());
    }
}

#[test]
fn nonempty_header_facts_keep_their_scope_and_prefix() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(NONEMPTY_PAIR);
    let p = declaration(&mut run);
    let header = SourcePosition::new(None, SourceOwner::StructHeader(p), 0);
    let id = p
        .introduced_params
        .as_ref()
        .unwrap()
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    assert!(header.visible_fact(id, &compiler.runtime).is_err());
    assert!(SourcePosition {
        before: 1,
        ..header
    }
    .visible_fact(id, &compiler.runtime)
    .is_ok());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(outside.visible_fact(id, &compiler.runtime).is_err());
}

#[test]
fn nonempty_structures_reject_empty_arguments_and_unsupported_finite_kinds() {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime
        .run_litex_code(
            "struct NonemptyPair<A nonempty_set>:\n    x A\n    y A\n$is_set(&NonemptyPair<{}>)\n",
        )
        .unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "empty_parameter")
        .is_err());

    let (run, compiler) = super::execute("struct FinitePair<A finite_set>:\n    x A\n    y A\n");
    assert!(compiler.compile_run(&run, "finite_parameter").is_err());
}

#[test]
fn struct_header_examples_preserve_actual_arguments_and_conditions() {
    for source in [
        PARAMETERIZED_PAIR,
        DESIGNATED_PAIR,
        include_str!("../../../lean/examples/parameterized_equal_pairs/statement.lit"),
        include_str!("../../../lean/examples/threshold_points/statement.lit"),
        include_str!("../../../lean/examples/chosen_parameterized_pairs/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "struct_headers")
            .unwrap_or_else(|e| panic!("{}: {e:?}", source.lines().next().unwrap()));
        assert_eq!(lean, compiler.compile_run(&run, "struct_headers").unwrap());
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn struct_headers_require_original_ordered_introductions() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(DESIGNATED_PAIR);
        let p = declaration(&mut run);
        match change {
            0 => p.introduced_params = None,
            1 => p
                .introduced_params
                .as_mut()
                .unwrap()
                .param_type_well_defined
                .clear(),
            2 => p
                .introduced_params
                .as_mut()
                .unwrap()
                .defined_params
                .store_and_infer_results
                .swap(0, 1),
            3 => p
                .statement
                .param_def_with_dom
                .as_mut()
                .unwrap()
                .0
                .groups
                .swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_header").is_err());
    }
}

#[test]
fn struct_specialization_requires_each_argument_wd_and_type_proof() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
    for change in 0..4 {
        let (mut run, compiler) = super::execute(DESIGNATED_PAIR);
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(p)),
            ..
        } = (&mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[1])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("struct WD");
        };
        match change {
            0 => p.child_obj_well_defined.clear(),
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => p.requirement_fact_verified.clear(),
            3 => p.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_arguments").is_err());
    }
}

#[test]
fn struct_header_facts_obey_original_scope_and_prefix() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(DESIGNATED_PAIR);
    // Borrow the original declaration only after the run is complete.
    let p = declaration(&mut run);
    let outer = SourcePosition::new(None, SourceOwner::StructHeader(p), 0);
    for (index, store) in p
        .introduced_params
        .as_ref()
        .unwrap()
        .defined_params
        .store_and_infer_results
        .iter()
        .enumerate()
    {
        let prior = SourcePosition {
            before: index,
            ..outer
        };
        let completed = SourcePosition {
            before: index + 1,
            ..outer
        };
        assert!(prior
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_err());
        assert!(completed
            .visible_fact(store.primary_fact_id(), &compiler.runtime)
            .is_ok());
    }
    let private = p
        .introduced_params
        .as_ref()
        .unwrap()
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(outside.visible_fact(private, &compiler.runtime).is_err());
}

#[test]
fn struct_published_laws_cannot_drop_header_parameters_or_type_premises() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(DESIGNATED_PAIR);
        let p = declaration(&mut run);
        let StoreFactResult::ForallFact(law) = &mut p.definition_facts[0].store_and_infer.store
        else {
            panic!("law");
        };
        match change {
            0 => {
                law.fact.typed_parameters.groups.remove(0);
            }
            1 => {
                law.fact.dom_facts.remove(0);
            }
            2 => law.fact.dom_facts.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "bad_header_publication")
            .is_err());
    }
}

#[test]
fn struct_specialization_cannot_erase_the_instantiated_field_carrier() {
    let source = "struct Pair<A set>:\n    x A\n    y A\n(1, -1) $in &Pair<N>\n";
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_natural_pair")
        .is_err());
}

const SUBSET_RETURN: &str =
    include_str!("../../../lean/examples/struct_subset_function_return/statement.lit");

#[test]
fn struct_signature_constructors_replay_headers_and_dependent_fields() {
    for source in [
        SUBSET_RETURN,
        include_str!("../../../lean/examples/struct_subset_function_input/statement.lit"),
        include_str!("../../../lean/examples/struct_guarded_subset_function/statement.lit"),
        include_str!("../../../lean/examples/struct_dependent_subset_function/statement.lit"),
        include_str!("../../../lean/examples/struct_nested_subset_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "field_signature").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "field_signature").unwrap());
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn struct_signature_constructors_require_original_field_formation() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SUBSET_RETURN);
        let p = declaration(&mut run);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                    wd,
                )),
            ..
        } = p.field_scope.fields[0]
            .well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("original function field formation");
        };
        match mutation {
            0 => super::replace_wd_subject(
                &mut wd.ret_set_well_defined,
                Obj::StandardSet(StandardSet::R),
            ),
            1 => wd.param_type_well_defined.clear(),
            2 => wd.defined_params.store_and_infer_results.clear(),
            3 => std::mem::swap(
                &mut wd.ret_set_well_defined,
                &mut wd.param_type_well_defined[0],
            ),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_field_signature")
            .expect_err("original field constructor evidence is required");
    }
}

#[test]
fn struct_signature_constructor_lookup_respects_parameter_and_publication_scope() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(SUBSET_RETURN);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) = &run.statement_results[1]
    else {
        panic!("forall statement");
    };
    let VerifyFactResult::ForallFact(result) = &result.verify_result else {
        panic!("forall proof");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
        result.as_ref()
    else {
        panic!("local forall");
    };
    let layer = &p
        .introduced_params
        .auto_opened_struct_layers
        .as_ref()
        .unwrap()[0];
    let carrier = layer
        .store_and_infer
        .iter()
        .find_map(|store| {
            let StoreFactResult::AtomicFact(stored) = &store.store else {
                return None;
            };
            let AtomicFact::InFact(member) = &stored.fact else {
                return None;
            };
            if !matches!(
                member.element,
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_))
            ) {
                return None;
            }
            let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
                return None;
            };
            Some(signature.ret_set.as_ref().clone())
        })
        .expect("released function-field carrier");
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler
        .compile_struct_field_constructor_reference(&carrier, &root)
        .unwrap()
        .is_none());
    // Automatic field release follows completion of the parameter header.
    let before_record = SourcePosition::new(Some(&root), SourceOwner::Forall(p), 3);
    assert!(compiler
        .compile_struct_field_constructor_reference(&carrier, &before_record)
        .unwrap()
        .is_none());
    let after_record = SourcePosition {
        before: 4,
        ..before_record
    };
    assert!(compiler
        .compile_struct_field_constructor_reference(&carrier, &after_record)
        .unwrap()
        .is_some());
    let after_forall = SourcePosition { before: 2, ..root };
    assert!(compiler
        .compile_struct_field_constructor_reference(&carrier, &after_forall)
        .unwrap()
        .is_none());
}

#[test]
fn struct_signature_constructors_retain_field_guards() {
    let valid = include_str!("../../../lean/examples/struct_guarded_subset_function/statement.lit");
    let invalid = format!("{valid}\nforall Carrier set, p &GuardedRecordOfSubsets<Carrier>:\n    $is_set(p.subsets(0))\n");
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(&invalid).unwrap();
    assert!(!run.success);
    crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "missing_field_guard")
        .expect_err("an undefined call cannot be compiled");
}

const NAMED_IDENTITY_LAW: &str =
    include_str!("../../../lean/examples/struct_named_identity_law/statement.lit");
const NESTED_GUARDED_IDENTITY_LAW: &str =
    include_str!("../../../lean/examples/struct_nested_guarded_identity_law/statement.lit");

#[test]
fn concrete_universal_record_predicates_replay_original_declarations() {
    for source in [
        NAMED_IDENTITY_LAW,
        NESTED_GUARDED_IDENTITY_LAW,
        include_str!("../../../lean/examples/struct_nonidentity_law/statement.lit"),
        include_str!("../../../lean/examples/struct_finite_subset_transfer/statement.lit"),
        include_str!("../../../lean/examples/category_identity_and_composition/statement.lit"),
        include_str!("../../../lean/examples/named_identity_function_domain/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "named_record_law")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "named_record_law").unwrap()
        );
    }
}

#[test]
fn concrete_universal_record_predicates_keep_canonical_binders_and_declaration_scope() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(NAMED_IDENTITY_LAW);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(declaration),
    )) = &run.statement_results[0]
    else {
        panic!("predicate declaration");
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        crate::execute::ExecDefStructStmtResult::Success(record),
    )) = &run.statement_results[1]
    else {
        panic!("record declaration");
    };
    let Fact::AtomicFact(fact) = &record.statement.equivalent_facts[0] else {
        panic!("named record law");
    };
    let Fact::ForallFact(law) = &declaration.statement.iff_facts[0] else {
        panic!("universal clause");
    };
    let id = law.typed_parameters.ordered_param_ids()[0].value();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let visible = SourcePosition {
        before: 1,
        ..before
    };
    let args = ["selected_mapping".into()];
    assert!(compiler
        .compile_atomic_raw_proposition(fact, &args, &before)
        .is_err());
    let meaning = compiler
        .compile_atomic_raw_proposition(fact, &args, &visible)
        .unwrap();
    assert!(meaning.contains(&format!("∀ (_value_i{id} : Litex.Obj (M := M) M.Value)")));
    assert!(!meaning.contains(&format!("∀ (_raw_i{id} : M.Value)")));
    compiler
        .compile_atomic_raw_proposition(fact, &[], &visible)
        .expect_err("the original predicate arity remains mandatory");
    let collisions = std::collections::HashMap::from([(
        law.typed_parameters.ordered_param_ids()[0],
        "captured_outer".into(),
    )]);
    compiler
        .compile_canonical_predicate_value(
            &declaration.statement.iff_facts[0],
            &visible,
            &collisions,
        )
        .expect_err("inner binders cannot capture an enclosing source identity");
}

#[test]
fn concrete_universal_record_predicates_require_original_guard_and_formation() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(NESTED_GUARDED_IDENTITY_LAW);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            crate::execute::ExecDefPropStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!("guarded predicate declaration");
        };
        if mutation == 0 {
            p.assumed_iff_facts.clear();
        } else {
            let FactWellDefinedProof::ForallFact(wd) = &mut p.assumed_iff_facts[0].well_defined
            else {
                panic!("universal formation");
            };
            let wd = wd.as_detailed_mut().unwrap();
            match mutation {
                1 => wd.then.clear(),
                2 => wd.assumed_dom_facts.clear(),
                3 => wd
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .clear(),
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "changed_predicate_formation")
            .expect_err("canonical rendering cannot replace original formation evidence");
    }
}

#[test]
fn concrete_universal_record_predicates_do_not_remove_call_domains() {
    let invalid = format!(
        "{NESTED_GUARDED_IDENTITY_LAW}\nforall p &GuardedIdentityRecord:\n    p.mapping(0) = 0\n"
    );
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(&invalid).unwrap();
    assert!(!run.success);
    crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_predicate_call")
        .expect_err("the named law retains its function's nonzero domain");
}
