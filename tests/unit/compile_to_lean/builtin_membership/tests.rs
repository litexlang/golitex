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
fn function_membership_replays_both_inclusions_for_release_and_selected_calls() {
    use crate::execute::execute_by_stmt::BuiltinFunctionDomainProof;
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    let (run, compiler) = super::execute(include_str!(
        "../../../../lean/examples/reordered_function_membership/statement.lit"
    ));
    for index in [1, 3] {
        let domain = match &run.statement_results[index] {
            ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) => &p.function_domain,
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => {
                &p.function_domain
            }
            _ => panic!("membership invocation"),
        };
        assert!(
            matches!(domain, Some(BuiltinFunctionDomainProof::Membership(p)) if matches!(p.comparison,FunctionDomainComparisonProof::MutualInclusion{..}))
        );
    }
    let lean = compiler
        .compile_run(&run, "reordered_function_membership")
        .unwrap();
    assert!(lean.contains("Litex.SetSemantics.ext"));
    assert!(lean.contains("Litex.FunctionSemantics.fnSet_of_returns"));
    assert_eq!(
        lean,
        compiler
            .compile_run(&run, "reordered_function_membership")
            .unwrap()
    );
}

#[test]
fn function_membership_replays_positive_domains_and_abstract_citations() {
    for source in [
        include_str!("../../../../lean/examples/positive_function_membership/statement.lit"),
        include_str!(
            "../../../../lean/examples/abstract_function_membership_domains/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "equivalent_function_domains")
            .unwrap();
        assert!(lean.contains("Litex.SetSemantics.ext"));
        assert!(lean.contains("Litex.FunctionSemantics.fnSet_of_returns"));
    }
}

#[test]
fn function_membership_rejects_swapped_inclusions_and_forged_alpha_comparisons() {
    use crate::execute::execute_by_stmt::BuiltinFunctionDomainProof;
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
    for index in [1, 3] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(include_str!(
                "../../../../lean/examples/reordered_function_membership/statement.lit"
            ));
            let domain = match &mut run.statement_results[index] {
                ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                    ExecReleaseThmStmtResult::Success(p),
                )) => &mut p.function_domain,
                ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => {
                    &mut p.function_domain
                }
                _ => panic!(),
            };
            let Some(BuiltinFunctionDomainProof::Membership(p)) = domain else {
                panic!()
            };
            let FunctionDomainComparisonProof::MutualInclusion {
                forward,
                forward_proof,
                reverse,
                reverse_proof,
            } = &mut p.comparison
            else {
                panic!()
            };
            match mutation {
                0 => {
                    std::mem::swap(forward, reverse);
                    std::mem::swap(forward_proof, reverse_proof);
                }
                1 => std::mem::swap(forward_proof, reverse_proof),
                2 => p.comparison = FunctionDomainComparisonProof::AlphaEquivalent,
                _ => unreachable!(),
            }
            assert!(
                compiler
                    .compile_run(&run, "invalid_function_domain")
                    .is_err(),
                "index {index}, mutation {mutation}"
            );
        }
    }
}

#[test]
fn function_membership_domain_comparison_cannot_cite_later_return_proofs() {
    use crate::execute::execute_by_stmt::BuiltinFunctionDomainProof;
    let (run, compiler) = super::execute(include_str!(
        "../../../../lean/examples/reordered_function_membership/statement.lit"
    ));
    for index in [1, 3] {
        let (owner, domain, id) = match &run.statement_results[index] {
            ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) => (
                SourceOwner::ThmRelease(p),
                &p.function_domain,
                p.dom_stores[0].primary_fact_id(),
            ),
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => (
                SourceOwner::Call(p),
                &p.function_domain,
                p.dom_stores[0].primary_fact_id(),
            ),
            _ => panic!(),
        };
        let Some(BuiltinFunctionDomainProof::Membership(domain)) = domain else {
            panic!()
        };
        let root = SourcePosition::new(None, SourceOwner::Run(&run), index);
        let stmt = SourcePosition::new(
            Some(&root),
            SourceOwner::Statement(&run.statement_results[index]),
            0,
        );
        let invocation = SourcePosition::new(Some(&stmt), owner, 0);
        let comparison =
            SourcePosition::new(Some(&invocation), SourceOwner::FunctionDomainWD(domain), 0);
        for stage in 0..2 {
            let prior = comparison.function_domain_comparison_prior(stage).unwrap();
            assert!(compiler.cited_fact_reference(id, &prior).is_err());
        }
        let after = SourcePosition {
            before: 1,
            ..invocation
        };
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
    }
}

#[test]
fn function_membership_does_not_erase_part_of_a_functions_domain() {
    let source = "have fn f(x R) R = x\nrelease thm fn_set_member(f,fn(y R: y > 0) C)\n";
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "restricted_domain")
        .is_err());
}

#[test]
fn function_membership_replays_complete_composition_domains() {
    use crate::execute::execute_by_stmt::BuiltinFunctionDomainProof;
    use crate::execute::execute_fact_stmt::function_domain::{
        CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
    };
    let (run, compiler) = super::execute(include_str!(
        "../../../../lean/examples/composed_quotient_membership/statement.lit"
    ));
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &run.statement_results[2]
    else {
        panic!()
    };
    let Some(BuiltinFunctionDomainProof::Membership(domain)) = &p.function_domain else {
        panic!()
    };
    assert!(matches!(
        domain.source.source,
        CompleteFunctionDomainSourceProof::Composition(_)
    ));
    assert!(matches!(
        domain.comparison,
        FunctionDomainComparisonProof::MutualInclusion { .. }
    ));
    let lean = compiler
        .compile_run(&run, "composed_quotient_member")
        .unwrap();
    assert!(lean.contains("Litex.composeInFnSet"));
    assert!(lean.contains("Litex.FunctionSemantics.fnSet_of_returns"));
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
