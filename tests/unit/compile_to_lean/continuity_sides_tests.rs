use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const LEFT: &str = r#"# Relate full and one-sided continuity at the same point of the complete domain.
thm checked_function_continuous_to_left:
    ? forall f fn(x R) R, p R:
        $is_continuous_at(f,p)
        =>:
            $is_continuous_left(f,p)
    release thm fn_continuous_at_to_left(f,p)
"#;
const RIGHT: &str = r#"# Relate full and one-sided continuity at the same point of the complete domain.
thm checked_function_continuous_to_right:
    ? forall f fn(x R) R, p R:
        $is_continuous_at(f,p)
        =>:
            $is_continuous_right(f,p)
    release thm fn_continuous_at_to_right(f,p)
"#;
const BOTH: &str = r#"# Relate full and one-sided continuity at the same point of the complete domain.
thm checked_function_continuous_from_sides:
    ? forall f fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_right(f,p)
        =>:
            $is_continuous_at(f,p)
    release thm fn_continuous_from_sides(f,p)
"#;
const CHAIN: &str = r#"# Compose the original side-restriction and recombination rules at one point.
thm checked_function_continuous_side_chain:
    ? forall f fn(x R) R, p R:
        $is_continuous_at(f,p)
        =>:
            $is_continuous_at(f,p)
    release thm fn_continuous_at_to_left(f,p)
    release thm fn_continuous_at_to_right(f,p)
    release thm fn_continuous_from_sides(f,p)
"#;

fn body(run: &mut RunLitexCodeResult) -> &mut ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!("forall body")
    };
    body
}

fn final_invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(call),
    )) = body(run).proof_steps.last_mut().unwrap()
    else {
        panic!("final release")
    };
    call
}

#[test]
fn continuity_sides_require_exact_original_stage_counts_without_an_invented_point_premise() {
    for source in [LEFT, RIGHT, BOTH] {
        for change in ["proof", "store", "wd", "extra_requirement", "type_proof"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            let expected = if source == BOTH { 5 } else { 4 };
            assert_eq!(call.dom_proofs.len(), expected);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                "extra_requirement" => {
                    let builtin = call.builtin.as_mut().unwrap();
                    builtin.requirements.push(builtin.requirements[3].clone());
                }
                _ => call.type_proofs.push(call.dom_proofs.pop().unwrap()),
            }
            compiler.compile_run(&run, change).expect_err(
                "replay exactly the original context, proofs, stores and conclusion WD",
            );
        }
    }
}

#[test]
fn continuity_sides_reject_changed_sides_subjects_and_swapped_premises() {
    for source in [LEFT, RIGHT, BOTH] {
        for change in [
            "premise_side",
            "conclusion_side",
            "function",
            "point",
            "order",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            let builtin = call.builtin.as_mut().unwrap();
            if change == "order" {
                builtin
                    .requirements
                    .swap(3, if source == BOTH { 4 } else { 2 });
            } else {
                let goal = if change == "conclusion_side" {
                    &mut builtin.conclusions[0]
                } else {
                    &mut builtin.requirements[3]
                };
                let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) = goal else {
                    panic!("continuity")
                };
                match change {
                    "function" => f.function = super::number_object("0"),
                    "point" => f.point = super::number_object("42"),
                    _ => {
                        f.side = match f.side {
                            RealApproachSide::Both => RealApproachSide::Left,
                            _ => RealApproachSide::Both,
                        }
                    }
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("exact original function, point, side and ordered premises required");
        }
    }
}

#[test]
fn continuity_sides_retain_original_point_membership_formation() {
    for change in ["missing", "point", "domain", "function"] {
        let (mut run, compiler) = super::execute(LEFT);
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut body(&mut run)
            .assumed_dom_facts
            .last_mut()
            .unwrap()
            .well_defined
        else {
            panic!("atomic WD")
        };
        let PredicateDomainProof::FunctionAnalysis(formation) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("original point formation")
        };
        if change == "missing" {
            formation.requirements.clear();
        } else if change == "function" {
            formation.function_domain.domain = Obj::StandardSet(StandardSet::RPos);
        } else {
            let Fact::AtomicFact(AtomicFact::InFact(member)) =
                &mut formation.requirements[0].requirement
            else {
                panic!("point member")
            };
            if change == "point" {
                member.element = super::number_object("42");
            } else {
                member.set = Obj::StandardSet(StandardSet::RPos);
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("point membership must be replayed from its exact original formation");
    }
}

#[test]
fn continuity_sides_known_formation_requires_prior_citation_and_both_argument_equalities() {
    for change in ["future", "function_equality", "point_equality"] {
        let (mut run, compiler) = super::execute(CHAIN);
        let call = final_invocation(&mut run);
        let future = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut call.conclusions_wd[0] else {
            panic!("atomic WD")
        };
        let PredicateDomainProof::ByKnownFact(cite) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("repeated continuity WD citation")
        };
        if change == "future" {
            cite.cite_fact_id = future;
        } else {
            cite.why_parameters_of_known_fact_are_equal_to_givens
                .remove(if change == "function_equality" { 0 } else { 1 });
        }
        compiler
            .compile_run(&run, change)
            .expect_err("follow the earlier original WD and both captured argument equalities");
    }
}

#[test]
fn continuity_sides_keep_real_function_context_and_guarded_complete_domain() {
    for change in [
        "input_carrier",
        "output_carrier",
        "proof_order",
        "store_order",
    ] {
        let (mut run, compiler) = super::execute(
            r#"# Relate full and one-sided continuity at the same point of the complete domain.
thm checked_function_continuous_guarded_to_left:
    ? forall f fn(x R+: x!=2) R, p R+:
        p!=2
        $is_continuous_at(f,p)
        =>:
            $is_continuous_left(f,p)
    release thm fn_continuous_at_to_left(f,p)
"#,
        );
        let call = invocation(&mut run);
        match change {
            "proof_order" => call.dom_proofs.swap(0, 1),
            "store_order" => call.dom_stores.swap(0, 1),
            _ => {
                let index = if change == "input_carrier" { 1 } else { 2 };
                let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) =
                    &mut call.builtin.as_mut().unwrap().requirements[index]
                else {
                    panic!("real context")
                };
                subset.right = Obj::StandardSet(StandardSet::C);
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain complete guarded domain and original ordered real context");
    }
}
