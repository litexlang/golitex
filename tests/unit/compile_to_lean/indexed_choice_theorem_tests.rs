use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    IndexCartObjWellDefinedProof, SetOperatorObjWellDefinedProofByDef,
};
use crate::prelude::*;
const FAMILY: &str = r#"# A family of nonempty sets has a choice function on its nonempty index domain.
thm checked_indexed_choice_from_family:
    ? forall T,S nonempty_set, g fn(k T) S:
        forall A S:
            $is_nonempty_set(A)
        =>:
            $is_nonempty_set(index_cart(T,S,g))
    release thm index_cart_nonempty_by_choice_from_family(index_cart(T,S,g))
"#;
const POINT: &str = r#"# Pointwise nonempty factors give a nonempty indexed Cartesian product.
thm checked_indexed_choice_pointwise:
    ? forall T,S nonempty_set, g fn(k T) S:
        forall k T:
            $is_nonempty_set(g(k))
        =>:
            $is_nonempty_set(index_cart(T,S,g))
    release thm index_cart_nonempty_by_choice_from_pointwise(index_cart(T,S,g))
"#;
fn original_cart_wd(run: &mut RunLitexCodeResult) -> &mut IndexCartObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let head = super::theorem_goal_wd_mut(named).as_detailed_mut().unwrap();
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut head.then[0] else {
        panic!("original nonempty conclusion formation")
    };
    let wd = &mut wd.as_detailed_mut().unwrap().well_defined_of_each_parameter[0];
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexCart(wd)),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("original IndexCart constructor")
    };
    wd
}
#[test]
fn indexed_choice_replays_both_original_nonempty_universal_schemas() {
    for (source, family) in [(FAMILY, true), (POINT, false)] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            invocation(&mut run).builtin.as_ref().unwrap().theorem,
            if family {
                BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily
            } else {
                BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise
            }
        );
        let output = compiler.compile_run(&run, "indexed_choice").unwrap();
        assert!(output.contains(if family {
            "Litex.indexCartNonemptyFamily"
        } else {
            "Litex.indexCartNonemptyPointwise"
        }));
        assert_eq!(
            output,
            compiler.compile_run(&run, "indexed_choice").unwrap()
        );
    }
}
#[test]
fn indexed_choice_requires_original_universal_store_arguments_and_conclusion_wd() {
    for source in [FAMILY, POINT] {
        for mutation in ["proof", "store", "arguments", "wd", "conclusion", "types"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                "proof" => p.dom_proofs.clear(),
                "store" => p.dom_stores.clear(),
                "arguments" => p.builtin.as_mut().unwrap().arguments.clear(),
                "wd" => p.conclusions_wd.clear(),
                "types" => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
                _ => {
                    let p = p.builtin.as_mut().unwrap();
                    let Obj::SetOperator(SetOperator::IndexCart(cart)) = &p.arguments[0] else {
                        panic!()
                    };
                    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) = &mut p.conclusions[0]
                    else {
                        panic!()
                    };
                    f.set = cart.index_set.as_ref().clone();
                }
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("native choice must consume the original complete release stages");
        }
    }
}
#[test]
fn indexed_choice_keeps_the_exact_carrier_binder_nonempty_factor_and_empty_guard_list() {
    for source in [FAMILY, POINT] {
        for mutation in ["carrier", "capture", "body", "empty", "guards", "retag"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run).builtin.as_mut().unwrap();
            if mutation == "retag" {
                p.theorem =
                    if p.theorem == BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily {
                        BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise
                    } else {
                        BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily
                    };
            } else {
                let extra = p.conclusions[0].clone();
                let Fact::ForallFact(point) = &mut p.requirements[0] else {
                    panic!()
                };
                match mutation {
                    "carrier" => {
                        point.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::R))
                    }
                    "capture" => {
                        let Obj::SetOperator(SetOperator::IndexCart(cart)) = &p.arguments[0] else {
                            panic!()
                        };
                        let Obj::Identifier(IdentifierObj::Plain { id, .. }) =
                            cart.family_fn.as_ref()
                        else {
                            panic!()
                        };
                        point.typed_parameters.groups[0].params[0].id = *id;
                    }
                    "empty" => point.then_facts.clear(),
                    "guards" => point.dom_facts.push(extra),
                    _ => {
                        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) =
                            &mut point.then_facts[0]
                        else {
                            panic!()
                        };
                        f.set = Obj::StandardSet(StandardSet::R);
                    }
                }
            }
            compiler.compile_run(&run, mutation).expect_err(
                "retain the uncaptured original universal family and factor nonemptiness",
            );
        }
    }
}
#[test]
fn indexed_choice_retains_original_index_family_nonemptiness_and_function_constructor_wd() {
    for source in [FAMILY, POINT] {
        for mutation in ["guard", "child", "swapped"] {
            let (mut run, compiler) = super::execute(source);
            let wd = original_cart_wd(&mut run);
            match mutation {
                "guard" => {
                    wd.requirement_fact_verified.pop();
                }
                "child" => {
                    wd.child_obj_well_defined.pop();
                }
                _ => wd.requirement_fact_verified.swap(0, 2),
            }
            compiler.compile_run(&run,mutation).expect_err("native choice cannot discard the source nonempty-index, nonempty-family or function WD");
        }
    }
}
#[test]
fn indexed_choice_cannot_cite_its_future_nonempty_product_in_constructor_requirements() {
    for source in [FAMILY, POINT] {
        let (mut run, compiler) = super::execute(source);
        let future = invocation(&mut run).builtin.as_ref().unwrap().conclusions[0].fact_id();
        let p =
            super::atomic_proof_mut(&mut original_cart_wd(&mut run).requirement_fact_verified[0]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut p.searched_proof
        else {
            panic!("original index nonempty citation")
        };
        p.cite_fact_id = future;
        compiler.compile_run(&run, "future").expect_err(
            "the original index must already be known nonempty before the product exists",
        );
    }
}
