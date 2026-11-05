use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_identities::ElementaryIdentitySearchProofByBuiltinRule as Rule;
use crate::prelude::*;

const FLOOR: &str = r#"thm checked_floor_bounds:
    ? forall x R,n Z:
        n<=x
        x<n+1
        =>:
            floor(x)=n
    floor(x)=n
"#;
const CEIL: &str = r#"thm checked_ceil_bounds:
    ? forall x R,n Z:
        x<=n
        n-1<x
        =>:
            ceil(x)=n
    ceil(x)=n
"#;

pub(super) fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut body.proof_steps[0] else {
        panic!()
    };
    super::equality_proof_mut(&mut p.verify_result)
}

fn children(
    p: &mut VerifyEqualitySuccess,
) -> (
    &mut VerifyFactResult,
    &mut VerifyFactResult,
    &mut VerifyFactResult,
) {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryIdentity(p),
    ) = &mut p.searched_proof
    else {
        panic!("selected elementary identity")
    };
    match p {
        Rule::FloorCharacterization(p) => (&mut p.integer, &mut p.weak_bound, &mut p.strict_bound),
        Rule::CeilCharacterization(p) => (&mut p.integer, &mut p.weak_bound, &mut p.strict_bound),
        _ => panic!("selected rounding characterization"),
    }
}

#[test]
fn rounding_characterization_replays_original_bounds_and_equalities() {
    for (source, law) in [
        (FLOOR, "floorFromIntegerBounds"),
        (CEIL, "ceilFromIntegerBounds"),
    ] {
        for source in [
            source.to_string(),
            source
                .replace("floor(x)=n", "n=floor(x)")
                .replace("ceil(x)=n", "n=ceil(x)"),
        ] {
            let (mut run, compiler) = super::execute(&source);
            let _ = children(equality(&mut run));
            let output = compiler
                .compile_run(&run, "rounding_bounds")
                .unwrap_or_else(|e| panic!("{e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "rounding_bounds").unwrap()
            );
        }
    }
}

#[test]
fn rounding_characterization_requires_the_three_original_children() {
    for source in [FLOOR, CEIL] {
        for change in ["order", "integer_subject", "strict_future", "shift"] {
            let (mut run, compiler) = super::execute(source);
            let p = equality(&mut run);
            let goal_id = p.fact.fact_id;
            let (integer, weak, strict) = children(p);
            match change {
                "order" => std::mem::swap(integer, weak),
                "integer_subject" => {
                    let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(integer).fact else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                }
                "strict_future" => {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut super::atomic_proof_mut(strict).searched_proof
                    else {
                        panic!()
                    };
                    cite.cite_fact_id = goal_id;
                }
                "shift" => {
                    let AtomicFact::LessFact(f) = &mut super::atomic_proof_mut(strict).fact else {
                        panic!()
                    };
                    let shift = if source == FLOOR {
                        &mut f.right
                    } else {
                        &mut f.left
                    };
                    let one = match shift {
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => &mut p.right,
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => &mut p.right,
                        _ => panic!(),
                    };
                    **one = Obj::Literal(Literal::Number(Number::new("2".into())));
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, change)
                .expect_err("original integer, weak and strict bounds are mandatory");
        }
    }
}

#[test]
fn rounding_certificate_cannot_change_its_operation() {
    let (mut floor, _) = super::execute(FLOOR);
    let (mut ceil, compiler) = super::execute(CEIL);
    std::mem::swap(
        &mut equality(&mut floor).searched_proof,
        &mut equality(&mut ceil).searched_proof,
    );
    compiler
        .compile_run(&ceil, "wrong_operation")
        .expect_err("floor evidence does not prove ceil characterization");
}

#[test]
fn rounding_strict_endpoints_cannot_be_weakened() {
    for source in [
        "forall x R,n Z:\n    n<=x\n    x<=n+1\n    =>:\n        floor(x)=n\n",
        "forall x R,n Z:\n    x<=n\n    n-1<=x\n    =>:\n        ceil(x)=n\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(source)
                .unwrap()
                .success
        );
    }
}
