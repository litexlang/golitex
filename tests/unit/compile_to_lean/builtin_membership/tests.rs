use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const BUILDER: &str = "release thm set_builder_member(1, {x R: x > 0})\n";
const DEFINED: &str =
    "let positives = {x R: x > 0}\nrelease thm defined_set_member(1, positives)\n";

#[test]
fn builtin_membership_replays_release_and_selected_invocations() {
    for source in [
        BUILDER, DEFINED,
        "by thm set_builder_member(1, {x R: x > 0}) => 1 $in {x R: x > 0}\n",
        "let positives = {x R: x > 0}\nby thm defined_set_member(1, positives) => 1 $in positives\n",
    ] {
        let (result, compiler) = super::execute(source);
        let output = compiler.compile_run(&result, "builtin_member").unwrap();
        assert!(output.contains("Litex.inSetBuilder_iff"));
        assert!(output.contains("Litex.SetSemantics M"));
        assert!(!output.contains("sorry") && !output.contains("axiom"));
    }
}

#[test]
fn builtin_membership_rejects_changed_arguments_premises_and_conclusion_formation() {
    for source in [BUILDER, DEFINED] {
        for change in ["argument", "premise", "formation", "store"] {
            let (mut result, compiler) = super::execute(source);
            let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(proof),
            )) = result.statement_results.last_mut().unwrap()
            else {
                panic!("release")
            };
            match change {
                "argument" => {
                    proof.builtin.as_mut().unwrap().arguments[0] = super::number_object("7")
                }
                "premise" => {
                    proof.dom_proofs.pop();
                }
                "formation" => {
                    proof.conclusions_wd.clear();
                }
                "store" => {
                    proof.dom_stores.clear();
                }
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&result, "bad_builtin_member").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn identical_premise_and_return_id_obeys_the_original_stage_boundary() {
    for source in [DEFINED, "let positives = {x R: x > 0}\nby thm defined_set_member(1, positives) => 1 $in positives\n"] {
        let (result, compiler) = super::execute(source);
        let (id, returned_id, owner) = match &result.statement_results[1] {
            ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(proof),
            )) => (proof.dom_stores[0].primary_fact_id(), proof.stored[0].primary_fact_id(), SourceOwner::ThmRelease(proof)),
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) =>
                (proof.dom_stores[0].primary_fact_id(), proof.returned_conclusions[0].primary_fact_id(), SourceOwner::Call(proof)),
            _ => panic!("theorem invocation"),
        };
        assert_eq!(id, returned_id);
        let run = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let stmt = SourcePosition::new(Some(&run), SourceOwner::Statement(&result.statement_results[1]), 0);
        let before = SourcePosition::new(Some(&stmt), owner, 0);
        assert!(before.visible_fact(id, &compiler.runtime).is_err());
        let after = SourcePosition { before: 1, ..before };
        let (_, reference) = after.visible_fact(id, &compiler.runtime).unwrap();
        assert_eq!(reference, format!("h_{}", id.value()));
    }
}

#[test]
fn selected_membership_publishes_its_inference_for_the_next_statement() {
    let source = include_str!("../../../../lean/examples/square_set_membership/statement.lit");
    let (result, compiler) = super::execute(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(last)) = &result.statement_results[2]
    else {
        panic!("final square inequality")
    };
    let VerifyFactResult::AtomicExceptEquality(last) = &last.verify_result else {
        panic!("inequality")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(last) = last.as_ref() else {
        panic!("successful inequality")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) = &last.searched_proof
    else {
        panic!("the final line cites the membership's inferred fact")
    };
    let output = compiler
        .compile_run(&result, "membership_inference")
        .unwrap();
    assert!(output.contains(&format!("theorem h_{}", citation.cite_fact_id.value())));
}

#[test]
fn cart_membership_theorem_preserves_the_complete_finite_domain() {
    let source = include_str!("../../../../lean/examples/cart_membership_theorem/statement.lit");
    let (result, compiler) = super::execute(source);
    let output = compiler.compile_run(&result, "cart_member").unwrap();
    assert!(output.contains("Litex.FunctionSemantics M"));
    assert!(output.contains("Litex.FiniteFunction.cart_of_coordinates"));
    for change in ["domain", "coordinate", "carrier", "comparison"] {
        let (mut result, compiler) = super::execute(source);
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) = &mut result.statement_results[0]
        else {
            panic!("release")
        };
        match change {
            "domain" => proof.function_domain = None,
            "coordinate" => {
                proof.builtin.as_mut().unwrap().requirements.pop();
            }
            "carrier" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut proof.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!("membership")
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            "comparison" => {
                let Some(crate::execute::execute_by_stmt::BuiltinFunctionDomainProof::Membership(
                    domain,
                )) = &mut proof.function_domain
                else {
                    panic!("domain")
                };
                domain.target.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R));
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&result, "bad_cart").is_err(),
            "{change}"
        );
    }
}

#[test]
fn function_membership_replays_original_guards_and_return_forall() {
    let source =
        include_str!("../../../../lean/examples/function_membership_theorem/statement.lit");
    let (result, compiler) = super::execute(source);
    let output = compiler.compile_run(&result, "fn_member").unwrap();
    assert!(output.contains("Litex.FunctionSemantics.fnSet_of_returns"));
    for change in ["domain", "return", "guard"] {
        let (mut result, compiler) = super::execute(source);
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) = result.statement_results.last_mut().unwrap()
        else {
            panic!("release")
        };
        match change {
            "domain" => proof.function_domain = None,
            "return" => proof.dom_proofs.clear(),
            "guard" => {
                let Some(crate::execute::execute_by_stmt::BuiltinFunctionDomainProof::Membership(
                    domain,
                )) = &mut proof.function_domain
                else {
                    panic!("domain")
                };
                domain.target.dom_facts.clear();
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&result, "bad_fn").is_err(), "{change}");
    }
}
