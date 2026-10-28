use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FiniteSeqSetObjWellDefinedProof, SetFormerObjWellDefinedProofByDef,
};
use crate::prelude::*;

fn sequence_wd(run: &mut RunLitexCodeResult) -> &mut FiniteSeqSetObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[0]
    else {
        panic!("let");
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(p)),
        ..
    }) = (&mut p.value_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!("finite sequence WD");
    };
    p
}

#[test]
fn finite_sequence_spaces_keep_generic_carriers_lengths_and_child_references() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_sequence_spaces/statement.lit"
    ));
    let output = compiler
        .compile_run(&run, "finite_sequence_spaces")
        .unwrap();
    assert!(output.contains("Litex.finiteSeq"));
    assert_eq!(
        output,
        compiler
            .compile_run(&run, "finite_sequence_spaces")
            .unwrap()
    );
}

#[test]
fn finite_sequence_coordinates_replay_original_function_membership() {
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_sequence_coordinates/statement.lit"
    ));
    let id = expansion(&mut run).derived.primary_fact_id();
    let output = compiler
        .compile_run(&run, "finite_sequence_coordinates")
        .unwrap();
    assert!(output.contains(&format!(
        "let _object_h{} := (Litex.fnSet (Litex.finiteSeqSignature",
        id.value()
    )));
    assert!(output.contains(&format!("have h_{} : Litex.In", id.value())));
}

fn expansion(
    run: &mut RunLitexCodeResult,
) -> &mut crate::store_fact_and_infer::InferInFactFiniteSeqExpandResult {
    use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};
    let proof = super::forall_proof_mut(&mut run.statement_results[0]);
    proof
        .introduced_params
        .defined_params
        .store_and_infer_results
        .iter_mut()
        .find_map(|store| {
            let store = std::rc::Rc::get_mut(store).expect("owned introduction");
            let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
                &mut store.infer
            else {
                return None;
            };
            rules.iter_mut().find_map(|rule| match rule {
                InferInFactResult::FiniteSeqExpand(p) => Some(p),
                _ => None,
            })
        })
        .expect("original finite-sequence expansion")
}

#[test]
fn finite_sequence_expansion_rejects_changed_receiver_domain_length_range_and_store_id() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/finite_sequence_coordinates/statement.lit"
        ));
        let p = expansion(&mut run);
        let StoreFactResult::AtomicFact(stored) = &mut p.derived.store else {
            panic!("membership")
        };
        let AtomicFact::InFact(member) = &mut stored.fact else {
            panic!("membership")
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set else {
            panic!("function set")
        };
        match mutation {
            0 => member.element = Obj::StandardSet(StandardSet::R),
            1 => {
                signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            2 => {
                let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                    signature.set_bound_parameters.groups[0].param_type.as_mut()
                else {
                    panic!("range")
                };
                range.end = range.start.clone();
            }
            3 => signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            4 => stored.fact_id = FactId::new(u64::MAX),
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_sequence_expansion")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn finite_sequence_wd_rejects_missing_swapped_and_changed_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute("let s = finite_seq(R, 2)\n");
        let p = sequence_wd(&mut run);
        match mutation {
            0 => p.child_obj_well_defined.clear(),
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => p.requirement_fact_verified.clear(),
            3 => p.requirement_fact_verified.swap(0, 1),
            4 => {
                let p = super::atomic_proof_mut(&mut p.requirement_fact_verified[1]);
                let AtomicFact::InFact(f) = &mut p.fact else {
                    panic!("natural length");
                };
                f.set = Obj::StandardSet(StandardSet::Z);
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_finite_sequence").is_err());
    }
}
