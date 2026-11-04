use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/nested_builder_shared_membership/statement.lit");
fn goal(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(
        &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
            .verify_result,
    )
}

#[test]
fn shared_builder_membership_publishes_nested_bounds_with_original_guarded_formation() {
    for source in [
        SOURCE,
        include_str!("../../../lean/examples/nested_builder_scalar_membership/statement.lit"),
        include_str!(
            "../../../lean/examples/nested_builder_guarded_bound_membership/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        let out = c
            .compile_run(&run, "nested_builder_shared")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains("Litex.inSetBuilder_iff"));
        assert_eq!(out, c.compile_run(&run, "nested_builder_shared").unwrap());
    }
}

#[test]
fn shared_builder_strategy_keeps_all_ordered_bound_and_filter_proofs() {
    for change in ["proof", "requirement", "order", "bound_subject"] {
        let (mut run, c) = super::execute(SOURCE);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderMembership(p),
        ) = &mut goal(&mut run).searched_proof
        else {
            panic!("actual shared builder strategy")
        };
        assert_eq!(p.requirement_facts.len(), 2);
        match change {
            "proof" => {
                p.proof_of_requirement_facts.pop();
            }
            "requirement" => {
                p.requirement_facts.pop();
            }
            "order" => p.proof_of_requirement_facts.swap(0, 1),
            _ => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirement_facts[0] else {
                    panic!("bound membership")
                };
                f.element = super::number_object("0");
            }
        }
        assert!(c.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn shared_builder_bound_replay_requires_the_exact_original_child_formation() {
    let (mut run, c) = super::execute(SOURCE);
    let wd = goal(&mut run).well_defined_proof.as_detailed_mut().unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(builder)),
        ..
    } = wd.well_defined_of_each_parameter[1]
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original outer builder formation")
    };
    let DetailedObjWellDefinedProof::ByDef { obj, .. } =
        builder.param_set_well_defined.as_detailed_mut().unwrap()
    else {
        panic!("original nested bound formation")
    };
    *obj = Obj::StandardSet(StandardSet::R);
    c.compile_run(&run, "changed_original_bound")
        .expect_err("original child WD subject required");
}
