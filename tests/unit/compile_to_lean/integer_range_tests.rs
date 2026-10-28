use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{ExecExpandRangeStmtResult, ExecExpandRangeStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const EXPAND: &str = "expand: 1 $in range(0, 3)\n";

fn expansion(statement: &mut ExecStmtResult) -> &mut ExecExpandRangeStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ExpandRange(
        ExecExpandRangeStmtResult::Success(p),
    )) = statement
    else {
        panic!("successful expansion")
    };
    p
}

#[test]
fn integer_range_expansion_replays_original_stores_deterministically() {
    let (mut run, compiler) = super::execute(EXPAND);
    let id = expansion(&mut run.statement_results[0])
        .stored
        .primary_fact_id();
    let lean = compiler.compile_run(&run, "integer_expansion").unwrap();
    assert!(lean.contains("Litex.inRangeInteger"));
    assert!(lean.contains(&format!("theorem h_{}", id.value())));
    assert!(lean.contains(
        "_range_integer = (0 : ℤ) ∨ _range_integer = (1 : ℤ) ∨ _range_integer = (2 : ℤ)"
    ));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "integer_expansion").unwrap()
    );
    assert!(lean.len() < 20_000);
}

#[test]
fn integer_range_expansion_rejects_incomplete_reordered_or_wrong_values() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(EXPAND);
        let p = expansion(&mut run.statement_results[0]);
        match mutation {
            0 => {
                p.values.pop();
            }
            1 => p.values.swap(0, 1),
            2 => p.values[0] = Obj::StandardSet(StandardSet::R),
            3 => p.values.push(p.values[0].clone()),
            4 => p.values.clear(),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_range_values").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn integer_range_expansion_rejects_changed_disjunction() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(EXPAND);
        let p = expansion(&mut run.statement_results[0]);
        let StoreFactResult::OrFact(store) = &mut p.stored.store else {
            panic!()
        };
        match mutation {
            0 => {
                store.fact.facts.pop();
            }
            1 => store.fact.facts.swap(0, 1),
            2 | 3 => {
                let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) =
                    &mut store.fact.facts[0]
                else {
                    panic!()
                };
                if mutation == 2 {
                    e.left = Obj::StandardSet(StandardSet::R);
                } else {
                    e.right = Obj::StandardSet(StandardSet::Z);
                }
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_range_store").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn integer_range_expansion_fact_is_visible_only_after_publication() {
    let (mut run, compiler) = super::execute(EXPAND);
    let id = expansion(&mut run.statement_results[0])
        .stored
        .primary_fact_id();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    for before in [0, 1] {
        let cursor = SourcePosition::new(
            Some(&root),
            SourceOwner::Statement(&run.statement_results[0]),
            before,
        );
        assert!(compiler.cited_fact_reference(id, &cursor).is_err());
    }
    let complete = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[0]),
        2,
    );
    assert!(compiler.cited_fact_reference(id, &complete).is_ok());
    let after = SourcePosition { before: 1, ..root };
    assert!(compiler.cited_fact_reference(id, &after).is_ok());
}

#[test]
fn integer_range_examples_cover_boundaries_arithmetic_and_reuse() {
    for source in [
        include_str!("../../../lean/examples/expand_half_open_integer_range/statement.lit"),
        include_str!("../../../lean/examples/expand_closed_integer_range/statement.lit"),
        include_str!("../../../lean/examples/expand_singleton_integer_range/statement.lit"),
        include_str!("../../../lean/examples/expand_calculated_integer_range/statement.lit"),
        include_str!("../../../lean/examples/integer_range_bounds/statement.lit"),
        include_str!("../../../lean/examples/integer_range_carriers_and_singletons/statement.lit"),
        include_str!("../../../lean/examples/integer_range_square_bound/statement.lit"),
        "expand: 0 $in closed_range(0, 0)\n",
        "sketch:\n    expand: 1 $in range(0, 3)\n",
        "$is_set(range(0, 0))\n1 $in range(0, 3)\n",
        "forall x closed_range(2, 2):\n    x = 2\n",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "range_example")
            .unwrap_or_else(|e| panic!("{source}\n{e}"));
        assert_eq!(lean, compiler.compile_run(&run, "range_example").unwrap());
        assert!(lean.len() < 100_000, "{} bytes: {source}", lean.len());
    }
}

#[test]
fn integer_range_constructor_requires_ordered_endpoint_wd_and_integer_evidence() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute("let interval = range(0, 3)\n");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let Some(DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::Range(p)),
            ..
        }) = (&mut p.value_well_defined)
            .as_detailed_success_mut()
            .unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.child_obj_well_defined.pop();
            }
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => {
                p.requirement_fact_verified.pop();
            }
            3 => p.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "invalid_range_wd").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn integer_range_rejects_excluded_endpoints_empty_expansion_and_excessive_expansion() {
    for source in [
        "3 $in range(0, 3)\n",
        "expand: 0 $in range(0, 0)\n",
        "expand: 1 $in range(0, 1025)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
        assert!(compiler.compile_run(&run, "rejected_range").is_err());
    }
}

#[test]
fn integer_range_membership_rejects_tampered_closed_calculation() {
    for field in 0..3 {
        let (mut run, compiler) = super::execute("1 $in range(0, 3)\n");
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
            ClosedAtomicExceptEqualityCalculationProof::In(
                ClosedMembershipCalculationProof::IntegerRange {
                    value, start, end, ..
                },
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        *match field {
            0 => value,
            1 => start,
            _ => end,
        } = ClosedScalarValue::Decimal("7".into());
        assert!(compiler.compile_run(&run, "bad_range_membership").is_err());
    }
}

#[test]
fn integer_range_inference_rejects_wrong_bounds_and_carriers() {
    for field in 0..5 {
        let (mut run, compiler) = super::execute("2 $in range(2, 3)\n");
        let stmt = super::fact_statement_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
            &mut stmt.store_and_infer_result.infer
        else {
            panic!()
        };
        let bounds = rules
            .iter_mut()
            .find_map(|rule| match rule {
                InferInFactResult::Range(p) => Some(&mut p.bounds),
                _ => None,
            })
            .unwrap();
        let store = match field {
            0 => &mut bounds.integer_membership.store,
            1 => &mut bounds.lower_bound.store,
            2 => &mut bounds.upper_bound.store,
            3 => &mut bounds.positive_membership.as_mut().unwrap().store,
            _ => &mut bounds.singleton_equality.as_mut().unwrap().store,
        };
        let StoreFactResult::AtomicFact(stored) = store else {
            panic!()
        };
        match &mut stored.fact {
            AtomicFact::InFact(f) => f.set = Obj::StandardSet(StandardSet::R),
            AtomicFact::LessEqualFact(f) => f.left = Obj::StandardSet(StandardSet::R),
            AtomicFact::LessFact(f) => f.right = Obj::StandardSet(StandardSet::R),
            AtomicFact::EqualFact(f) => f.right = Obj::StandardSet(StandardSet::R),
            _ => panic!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_range_inference").is_err(),
            "field {field}"
        );
    }
}
