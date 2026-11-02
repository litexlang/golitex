use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;
const GENERIC: &str =
    include_str!("../../../lean/examples/family_intersection_member_facts/statement.lit");
const SINGLETON: &str =
    include_str!("../../../lean/examples/family_intersection_singleton_member/statement.lit");
#[test]
fn intersection_facts_replays_original_member_and_publishes_usable_forall() {
    for source in [GENERIC, SINGLETON] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            invocation(&mut run).builtin.as_ref().unwrap().theorem,
            BuiltinTheoremId::FamilyIntersectionMemberFacts
        );
        let output = compiler.compile_run(&run, "intersection_facts").unwrap();
        assert!(output.contains("Litex.familyIntersect_members"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "intersection_facts").unwrap()
        );
    }
}
#[test]
fn intersection_facts_requires_all_original_ordered_proofs_stores_args_and_forall_wd() {
    for source in [GENERIC, SINGLETON] {
        for mutation in [
            "proof",
            "store",
            "swap_proof",
            "swap_store",
            "arguments",
            "wd",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "swap_proof" => p.dom_proofs.swap(0, 2),
                "swap_store" => p.dom_stores.swap(0, 2),
                "arguments" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => p.conclusions_wd.clear(),
            }
            compiler.compile_run(&run, mutation).expect_err(
                "retain exact source membership elimination stages and forall formation",
            );
        }
    }
}
#[test]
fn intersection_facts_preserves_factor_domain_binder_set_guard_and_member_subject() {
    for mutation in [
        "domain",
        "capture",
        "guard",
        "body",
        "element",
        "requirement",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == "requirement" {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::ForallFact(point) = &mut p.conclusions[0] else {
                panic!()
            };
            match mutation {
                "domain" => {
                    point.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                "capture" => {
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &p.arguments[0] else {
                        panic!()
                    };
                    point.typed_parameters.groups[0].params[0].id = *id;
                }
                "guard" => point.dom_facts.clear(),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut point.then_facts[0]
                    else {
                        panic!()
                    };
                    if mutation == "body" {
                        f.set = Obj::StandardSet(StandardSet::R);
                    } else {
                        f.element = Obj::Literal(Literal::Number(Number::new("0".into())));
                    }
                }
            }
        }
        compiler.compile_run(&run, mutation).expect_err(
            "exact original guarded factor conclusion and required intersection member",
        );
    }
}
#[test]
fn intersection_facts_retains_required_member_wd_and_forall_binder_formation() {
    for mutation in ["member", "binder", "body"] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run);
        if mutation == "member" {
            super::atomic_proof_mut(&mut p.dom_proofs[2])
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else {
            let FactWellDefinedProof::ForallFact(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let wd = wd.as_detailed_mut().unwrap();
            if mutation == "binder" {
                wd.introduced_params.param_type_well_defined.clear();
            } else {
                wd.then.clear();
            }
        }
        compiler.compile_run(&run, mutation).expect_err(
            "reuse captured membership construction locally without replacing conclusion WD",
        );
    }
}
#[test]
fn intersection_facts_cannot_cite_the_future_forall_as_its_input_membership() {
    let (mut run, compiler) = super::execute(GENERIC);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
        &mut super::atomic_proof_mut(&mut p.dom_proofs[2]).searched_proof
    else {
        panic!("original typed intersection member citation")
    };
    cite.cite_fact_id = future;
    compiler
        .compile_run(&run, "future")
        .expect_err("the intersection membership must precede its factor forall");
}
