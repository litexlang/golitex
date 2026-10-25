#[test]
fn composition_right_identity_replays_mutual_domain_inclusion() {
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_composition::CompositionEqualityProof;
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/reordered_function_domains/statement.lit"
    ));
    let CompositionEqualityProof::RightIdentity(p) = composition_law(&mut run, 2) else {
        panic!();
    };
    assert!(matches!(
        p.full_domain.comparison,
        FunctionDomainComparisonProof::MutualInclusion { .. }
    ));
    let lean = compiler.compile_run(&run, "reordered_domains").unwrap();
    assert!(lean.contains("Litex.composeRightIdentity"));
    assert!(lean.contains("Litex.SetSemantics.ext"));
}

#[test]
fn strict_composition_formation_replays_original_compatibility() {
    let (run, compiler) = super::execute("have fn comp_square(t R) R = t^2\nhave fn comp_gap(x,y R: x<y) R = y-x\n$is_set(comp_square ∘ comp_gap)\n");
    let lean = compiler.compile_run(&run, "composition_formation").unwrap();
    assert!(lean.contains("Litex.compose "));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "composition_formation").unwrap()
    );
}

use crate::execute::execute_fact_stmt::function_composition::CompositionObjWellDefinedProof;
use crate::prelude::*;

const FORMATION: &str = "have fn comp_square(t R) R = t^2\nhave fn comp_gap(x,y R: x<y) R = y-x\n$is_set(comp_square ∘ comp_gap)\n";

fn construction(run: &mut RunLitexCodeResult) -> &mut CompositionObjWellDefinedProof {
    let fact = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[2]).verify_result,
    );
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::Composition(
                p,
            )),
        ..
    } = &mut fact.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("composition constructor")
    };
    p
}

#[test]
fn composition_rejects_changed_operand_domain_body_and_compatibility_evidence() {
    for change in 0..6 {
        let (mut run, compiler) = super::execute(FORMATION);
        let p = construction(&mut run);
        match change {
            0 => std::mem::swap(&mut p.outer_well_defined, &mut p.inner_well_defined),
            1 => p.inner_domain.signature.dom_facts.clear(),
            2 => p.function.body.dom_facts.clear(),
            3 => p.function.equal_to = Box::new(super::number_object("17")),
            4 => p.outer_domain.signature.ret_set = Box::new(super::number_object("17")),
            5 => {
                let ObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::FunctionSpace(
                            FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(f),
                        ),
                    ..
                } = p.function_well_defined.as_mut()
                else {
                    panic!()
                };
                let ObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                } = f.body_well_defined.as_mut()
                else {
                    panic!()
                };
                call.requirement_fact_verified.clear();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_composition").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn composition_examples_replay_the_selected_calls_and_beta_steps() {
    for source in [
        include_str!("../../../lean/examples/squared_gap_composition/statement.lit"),
        include_str!("../../../lean/examples/shifted_square_composition/statement.lit"),
        include_str!("../../../lean/examples/double_reciprocal_composition/statement.lit"),
        include_str!("../../../lean/examples/abstract_function_composition/statement.lit"),
        include_str!("../../../lean/examples/positive_domain_composition/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "composition_variants").unwrap();
        assert!(lean.contains("Litex.composeCall"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "composition_variants").unwrap()
        );
    }
}

#[test]
fn composition_call_rejects_missing_argument_or_guard_stages() {
    let source = include_str!("../../../lean/examples/squared_gap_composition/statement.lit");
    for change in 0..3 {
        let (mut run, compiler) = super::execute(source);
        let eq = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[3]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(p),
            ..
        } = &mut eq.well_defined_proof.left
        else {
            panic!()
        };
        match change {
            0 => {
                p.child_obj_well_defined.pop();
            }
            1 => {
                p.requirement_fact_verified.pop();
            }
            2 => p.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_composition_call").is_err());
    }
}

#[test]
fn incompatible_composition_does_not_compile_a_silently_restricted_domain() {
    let source="have fn comp_inverse(x R: x != 0) R = 1/x\nhave fn comp_identity(x R) R = x\n$is_set(comp_inverse ∘ comp_identity)\n";
    let command =
        super::parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "incompatible")
        .is_err());
}

#[test]
fn composition_beta_rejects_changed_body_continuation_or_selected_composition() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
            normalize_function_body::FunctionBodyExpansionProof},
    };
    for change in 0..4 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/squared_gap_composition/statement.lit"
        ));
        let eq = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[3]).verify_result,
        );
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(p),
            ),
        ) = &mut eq.searched_proof
        else {
            panic!("recorded normalization")
        };
        let step = p
            .normalization
            .expansions
            .iter_mut()
            .find_map(|e| match e {
                FunctionBodyExpansionProof::Composition(p) => Some(p),
                _ => None,
            })
            .expect("composition beta step");
        match change {
            0 => step.expanded_body = super::number_object("17"),
            1 => step.continued_body = super::number_object("17"),
            2 => std::mem::swap(&mut step.composition.outer, &mut step.composition.inner),
            3 => step.function_equal.path[0].2 = FactId::new(u64::MAX),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_composition_beta").is_err());
    }
}

#[test]
fn composition_graph_laws_replay_selected_builtin_certificates() {
    for source in [
        include_str!("../../../lean/examples/composition_graph_laws/statement.lit"),
        include_str!("../../../lean/examples/guarded_composition_identities/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "composition_laws").unwrap();
        assert!(lean.contains("Litex.composeRightIdentity"));
        assert!(lean.contains("Litex.composeRangeSubset"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "composition_laws").unwrap()
        );
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_composition::CompositionEqualityProof;
fn composition_law(run: &mut RunLitexCodeResult, index: usize) -> &mut CompositionEqualityProof {
    let eq = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[index]).verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Composition(p)) =
        &mut eq.searched_proof
    else {
        panic!("selected composition builtin")
    };
    p
}

#[test]
fn composition_associativity_replays_both_original_orientations() {
    let definitions = "have fn comp_square(t R) R = t^2\nhave fn comp_shift(t R) R = t+1\n";
    for goal in [
        "(comp_square ∘ comp_shift) ∘ comp_shift = comp_square ∘ (comp_shift ∘ comp_shift)",
        "comp_square ∘ (comp_shift ∘ comp_shift) = (comp_square ∘ comp_shift) ∘ comp_shift",
    ] {
        let (mut run, compiler) = super::execute(&format!("{definitions}{goal}\n"));
        assert!(matches!(
            composition_law(&mut run, 2),
            CompositionEqualityProof::Associativity(_)
        ));
        assert!(compiler
            .compile_run(&run, "assoc_orientation")
            .unwrap()
            .contains("composition_associative"));
    }
}

#[test]
fn composition_fixed_laws_reject_changed_graphs_identities_and_citations() {
    for change in 0..5 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/composition_graph_laws/statement.lit"
        ));
        match (
            change,
            composition_law(
                &mut run,
                if change == 0 {
                    3
                } else if change <= 2 {
                    5
                } else {
                    6
                },
            ),
        ) {
            (0, CompositionEqualityProof::Associativity(p)) => {
                p.left.inner = Box::new(super::number_object("17"))
            }
            (1, CompositionEqualityProof::LeftIdentity(p)) => {
                p.identity.equal_to = Box::new(super::number_object("17"))
            }
            (2, CompositionEqualityProof::LeftIdentity(p)) => {
                p.identity_equal.path[0].2 = FactId::new(u64::MAX)
            }
            (3, CompositionEqualityProof::RightIdentity(p)) => {
                p.identity_equal.path[0].2 = FactId::new(u64::MAX)
            }
            (4, CompositionEqualityProof::RightIdentity(p)) => {
                p.full_domain.source.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::C))
            }
            _ => panic!("selected identity law"),
        }
        assert!(
            compiler.compile_run(&run, "bad_composition_law").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn composition_right_identity_rejects_removed_original_nonzero_domain() {
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/guarded_composition_identities/statement.lit"
    ));
    let CompositionEqualityProof::RightIdentity(p) = composition_law(&mut run, 2) else {
        panic!()
    };
    p.full_domain.target.dom_facts.clear();
    assert!(compiler.compile_run(&run, "bad_identity_domain").is_err());
}

#[test]
fn composition_definition_rejects_changed_body_and_domain() {
    for change in 0..2 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/composition_graph_laws/statement.lit"
        ));
        let CompositionEqualityProof::Definition(p) = composition_law(&mut run, 10) else {
            panic!()
        };
        if change == 0 {
            p.function.equal_to = Box::new(super::number_object("17"));
        } else {
            p.function.body.dom_facts.clear();
        }
        assert!(compiler
            .compile_run(&run, "bad_composition_definition")
            .is_err());
    }
}

#[test]
fn composition_range_subset_rejects_another_outer_function() {
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/composition_graph_laws/statement.lit"
    ));
    let fact = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[7]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(
            SubsetFactSearchProofByBuiltinRule::CompositionRangeSubset(p),
        ),
    ) = &mut fact.searched_proof
    else {
        panic!("selected range law")
    };
    std::mem::swap(
        &mut p.callable.composition.outer,
        &mut p.callable.composition.inner,
    );
    assert!(compiler.compile_run(&run, "bad_composition_range").is_err());
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule;

#[test]
fn composition_right_identity_does_not_erase_a_strict_domain_restriction() {
    let source =
        "have fn shift(x R) R = x+1\nhave fn nz_id(x R: x != 0) R = x\nshift ∘ nz_id = shift\n";
    let command =
        super::parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "wrong_identity_domain")
        .is_err());
}
