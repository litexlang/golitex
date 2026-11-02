use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

const SELECTED: &str =
    include_str!("../../../lean/examples/range_sum_bijective_enumerations/statement.lit");
const RELEASE: &str =
    include_str!("../../../lean/examples/range_sum_bijective_enumerations_release/statement.lit");

#[test]
fn enumeration_sum_replays_named_callback_equations_and_both_original_bijections() {
    for source in [
        SELECTED,
        RELEASE,
        include_str!(
            "../../../lean/examples/range_sum_bijective_enumerations_general/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "enumeration_sum").unwrap();
        assert!(output.contains("Litex.rangeSumNamedEnumerationValue"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "enumeration_sum").unwrap()
        );
    }
    let (mut run, _) = super::execute(RELEASE);
    assert_eq!(
        invocation(&mut run).builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::SumOverBijectiveFiniteSetEnumerations
    );
}

#[test]
fn enumeration_sum_requires_nine_original_ordered_prerequisites_and_conclusion_wd() {
    for change in [
        "args",
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "types",
        "requirements",
    ] {
        let (mut run, compiler) = super::execute(RELEASE);
        let p = invocation(&mut run);
        match change {
            "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "proof" => {
                p.dom_proofs.pop();
            }
            "proof_order" => p.dom_proofs.swap(7, 8),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 1),
            "wd" => p.conclusions_wd.clear(),
            "types" => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
            _ => {
                p.builtin.as_mut().unwrap().requirements.pop();
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain every original enumeration-sum prerequisite and publication");
    }
}

#[test]
fn enumeration_sum_keeps_exact_composition_binder_domain_and_empty_guards() {
    for change in ["body", "binder", "domain", "guards"] {
        let (mut run, compiler) = super::execute(RELEASE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(extra) = b.requirements[6].clone() else {
            panic!("original finite-target requirement")
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut b.requirements[0] else {
            panic!()
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut eq.right else {
            panic!()
        };
        match change {
            "body" => f.equal_to = Box::new(Obj::StandardSet(StandardSet::R)),
            "binder" => {
                let Obj::FnObj(outer) = f.equal_to.as_ref() else {
                    panic!()
                };
                let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) = outer.head.as_ref()
                else {
                    panic!()
                };
                f.body.set_bound_parameters.groups[0].params[0].id = *id;
            }
            "domain" => {
                f.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::Z))
            }
            _ => f.body.dom_facts.push(QuantifierFreeFact::AtomicFact(extra)),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("do not replace or capture either original enumeration composition");
    }
}

#[test]
fn enumeration_sum_preserves_original_finite_target_and_bijection_contracts() {
    for change in ["finite", "domain", "codomain", "function"] {
        let (mut run, compiler) = super::execute(RELEASE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "finite" {
            let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) = &mut b.requirements[6] else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::AtomicFact(AtomicFact::BijectiveFact(f)) = &mut b.requirements[8] else {
                panic!()
            };
            match change {
                "domain" => f.domain = Obj::StandardSet(StandardSet::Z),
                "codomain" => f.codomain = Obj::StandardSet(StandardSet::R),
                _ => f.function = Obj::StandardSet(StandardSet::R),
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("the checked finite codomain and two exact bijections are mandatory");
    }
}

#[test]
fn enumeration_sum_retains_original_callback_and_callable_formation() {
    for change in ["callback", "callable", "bijection_children"] {
        let (mut run, compiler) = super::execute(RELEASE);
        let p = invocation(&mut run);
        if change == "callback" {
            let VerifyFactResult::Equality(eq) = &mut p.dom_proofs[0] else {
                panic!()
            };
            let VerifyEqualityResult::Success(eq) = eq.as_mut() else {
                panic!()
            };
            super::replace_wd_subject(
                &mut eq.well_defined_proof.as_detailed_mut().unwrap().right,
                Obj::StandardSet(StandardSet::R),
            );
        } else {
            let p = super::atomic_proof_mut(&mut p.dom_proofs[8]);
            let wd = p.well_defined_proof.as_detailed_mut().unwrap();
            if change == "bijection_children" {
                wd.well_defined_of_each_parameter.clear();
            } else {
                match &mut wd.predicate_domain {
                    PredicateDomainProof::ByRequirements(r) => {
                        r.pop();
                    }
                    PredicateDomainProof::ByKnownFact(p) => p.cite_fact_id = FactId::new(u64::MAX),
                    _ => panic!("original callable formation"),
                }
            }
        }
        compiler.compile_run(&run, change).expect_err("bijection alone cannot replace the original callable signature or callback constructor WD");
    }
}

#[test]
fn enumeration_sum_cannot_cite_its_future_equality_in_an_original_callback_definition() {
    let (mut run, compiler) = super::execute(RELEASE);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let VerifyFactResult::Equality(eq) = &mut p.dom_proofs[0] else {
        panic!()
    };
    let VerifyEqualityResult::Success(eq) = eq.as_mut() else {
        panic!()
    };
    eq.searched_proof =
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(KnownEqualityPathProof::new(vec![
                (eq.fact.left.clone(), eq.fact.right.clone(), future),
            ])),
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("callback equations precede the reindexed sum conclusion");
}
