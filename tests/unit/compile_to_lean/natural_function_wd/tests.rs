use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AnonymousFnObjWellDefinedProof;
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult, StoreInferredFactResult};
use std::rc::Rc;

const DECLARATION: &str = "have fn f(x N) N = x + 1\n";

fn function(result: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(proof),
    )) = result
    else {
        panic!("successful natural function declaration")
    };
    proof
}

fn anonymous(result: &mut ExecStmtResult) -> &mut AnonymousFnObjWellDefinedProof {
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = &mut function(result).anonymous_fn_well_defined
    else {
        panic!("original anonymous function WD")
    };
    proof
}

fn nonnegative(proof: &mut AnonymousFnObjWellDefinedProof) -> &mut StoreInferredFactResult {
    let store = Rc::get_mut(&mut proof.defined_params.store_and_infer_results[0]).unwrap();
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
    else {
        panic!("original parameter membership inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(proof) => {
                assert_eq!(proof.derived.len(), 1);
                Some(&mut proof.derived[0])
            }
            _ => None,
        })
        .unwrap()
}

#[test]
fn natural_function_wd_retains_the_original_nonnegative_constructor() {
    let (mut result, compiler) = super::execute(DECLARATION);
    let capture = nonnegative(anonymous(&mut result.statement_results[0]));
    let StoreFactResult::AtomicFact(stored) = &capture.store else {
        panic!("original nonnegative store")
    };
    let AtomicFact::LessEqualFact(bound) = &stored.fact else {
        panic!("original 0 <= x inference")
    };
    let zero = bound.left.clone();
    assert_eq!(zero.ir(), super::number_object("0").ir());
    assert_eq!(capture.store.stored_fact_ids().len(), 1);
    let output = super::compile_run(&result, &compiler, "natural_constructor_capture")
        .expect("standalone formula declaration consumes the named natural rule");
    assert!(output.contains("Litex.formulaFn") && output.contains("Litex.naturalNonnegative"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn natural_function_wd_replays_scalar_identity_and_closed_evaluation() {
    for source in [
        "have fn f(x N) N=x+1\nhave n N\n2*f(n)=2+2*n\n",
        "have fn f(x N) N=x+1\nf(2)=3\n",
        include_str!("../../../../lean/examples/natural_successor_affine_identity/statement.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution.lit"),
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "natural_successor")
            .expect("the unchanged formula and its checked applications compile");
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn natural_function_wd_rejects_wrong_captured_return_membership_children() {
    for change in ["carrier", "left", "right"] {
        let (mut result, compiler) = super::execute(DECLARATION);
        let AnonymousFnBodyInReturnSetProof::CheckedMembership(membership) =
            &mut anonymous(&mut result.statement_results[0]).body_in_ret_set
        else {
            panic!("the checked natural return membership")
        };
        let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
            &mut super::atomic_proof_mut(membership).searched_proof
        else {
            panic!("the original structural natural addition proof")
        };
        let StructuralMembershipReason::Add { left, right } = &mut proof.reason else {
            panic!("the original return membership adds two natural operands")
        };
        match change {
            "carrier" => left.set = StandardSet::R,
            "left" => left.element = super::number_object("7"),
            "right" => right.element = super::number_object("2"),
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["StructuralMembership/ArithmeticChild"],
        );
    }
}

#[test]
fn natural_function_wd_replays_natural_multiplication_and_integer_addition() {
    for (source, law) in [
        ("have fn double(x N) N=2*x\n", "Litex.mulInN"),
        ("have fn successor(x Z) Z=x+1\n", "Litex.addInZ"),
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "numeric_closure")
            .expect("the actual structural carrier evidence is supported");
        assert!(output.contains(law));
    }
}

#[test]
fn natural_function_wd_preserves_return_types_call_domains_and_false_goals() {
    for source in [
        "have fn bad(x N) N=x-1\n",
        "have fn f(x N) N=x+1\nf(-1)=0\n",
        "have fn f(x N) N=x+1\nf(2)=4\n",
        "have fn reciprocal(t R: t!=0) R=1/t\nreciprocal(0)=0\n",
    ] {
        let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()])
            .expect("strict source boundary");
        let mut runtime = Runtime::new(command);
        let result = runtime.run_litex_code(source).unwrap();
        assert!(!result.success && result.session_error.is_none());
    }
}

#[test]
fn natural_function_inference_rejects_a_wrong_named_conclusion() {
    let (mut result, compiler) = super::execute(DECLARATION);
    let capture = nonnegative(anonymous(&mut result.statement_results[0]));
    let StoreFactResult::AtomicFact(stored) = &mut capture.store else {
        panic!("nonnegative store")
    };
    let AtomicFact::LessEqualFact(bound) = &mut stored.fact else {
        panic!("natural consequence")
    };
    bound.left = super::number_object("7");
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_named_conclusion",
        &["Inference/NaturalSubject", "Store/Subject"],
    );
}
