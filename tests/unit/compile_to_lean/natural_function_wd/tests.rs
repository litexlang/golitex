use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AnonymousFnObjWellDefinedProof;
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
    StoreInferredFactResult,
};
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
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) =
        &mut store.infer
    else {
        panic!("original parameter membership inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(proof) => {
                assert_eq!(proof.derived.len(), 1);
                Some(&mut proof.derived[0])
            }
            _ => None,
        })
        .unwrap()
}

fn zero_wd(proof: &mut StoreInferredFactResult) -> &mut ObjWellDefinedProof {
    let FactWellDefinedProof::AtomicExceptEquality(formation) = &mut proof.well_defined else {
        panic!("original nonnegative atomic formation")
    };
    &mut formation.well_defined_of_each_parameter[0]
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
    assert!(matches!(zero_wd(capture), ObjWellDefinedProof::ByDef {
        obj,
        proof: ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(_)),
    } if obj.ir() == zero.ir()));
    let output = super::compile_run(&result, &compiler, "natural_constructor_capture")
        .expect("standalone formula declaration consumes original zero WD");
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
fn natural_function_wd_rejects_deleted_or_reordered_constructor_capture() {
    for change in ["deleted", "reordered"] {
        let (mut result, compiler) = super::execute(DECLARATION);
        let capture = nonnegative(anonymous(&mut result.statement_results[0]));
        let FactWellDefinedProof::AtomicExceptEquality(formation) = &mut capture.well_defined
        else {
            panic!("atomic formation")
        };
        match change {
            "deleted" => formation.well_defined_of_each_parameter.clear(),
            "reordered" => formation.well_defined_of_each_parameter.swap(0, 1),
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["WD/"]);
    }
}

#[test]
fn natural_function_wd_rejects_wrong_or_missing_constructor_subject() {
    for change in ["wrong", "missing"] {
        let (mut result, compiler) = super::execute(DECLARATION);
        let wd = zero_wd(nonnegative(anonymous(&mut result.statement_results[0])));
        match change {
            "wrong" => match wd {
                ObjWellDefinedProof::ByDef { obj, .. } => *obj = super::number_object("1"),
                _ => panic!("original numeric constructor"),
            },
            "missing" => {
                *wd = ObjWellDefinedProof::ByKnown {
                    obj: super::number_object("0"),
                    wd_id: WellDefinednessId::new(u64::MAX),
                }
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["WD/", "WdId/"]);
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
fn natural_function_wd_rejects_a_future_zero_constructor() {
    let (mut result, compiler) = super::execute("have fn f(x N) N=x+1\n0=0\n");
    let zero = super::number_object("0");
    let future = compiler
        .runtime
        .well_defined_visible_in_stack(&zero)
        .expect("later top-level equality cached zero WD");
    *zero_wd(nonnegative(anonymous(&mut result.statement_results[0]))) =
        ObjWellDefinedProof::ByKnown {
            obj: zero,
            wd_id: future,
        };
    super::phase2_rejected(&result, &compiler, "future_zero", &["WD/Producer"]);
}

#[test]
fn natural_function_wd_rejects_a_closed_function_scope_wd_id() {
    let (mut result, compiler) = super::execute("have fn g(y N) N=y+1\nhave fn f(x N) N=x+1\n");
    let zero = super::number_object("0");
    let closed = anonymous(&mut result.statement_results[0])
        .local_env
        .well_defined_objects
        .object_to_wd_id[&zero.ir()];
    *zero_wd(nonnegative(anonymous(&mut result.statement_results[1]))) =
        ObjWellDefinedProof::ByKnown {
            obj: zero,
            wd_id: closed,
        };
    super::phase2_rejected(&result, &compiler, "closed_zero_id", &["WdId/Resolution"]);
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
