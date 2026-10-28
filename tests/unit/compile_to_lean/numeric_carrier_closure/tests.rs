use crate::execute::ExecHaveFnEqualStmtResult;
use crate::prelude::*;

#[test]
fn numeric_formula_returns_replay_their_selected_carrier_laws() {
    for (carrier, operation, expression, law) in [
        ("N", "add", "x+y", "addInN"),
        ("N", "mul", "x*y", "mulInN"),
        ("N", "pow", "x^2", "powStructuralInN"),
        ("Z", "add", "x+y", "addInZ"),
        ("Z", "sub", "x-y", "subInZ"),
        ("Z", "mul", "x*y", "mulInZ"),
        ("Z", "neg", "-x", "negInZ"),
        ("Z", "pow", "x^2", "powStructuralInZ"),
        ("Q", "add", "x+y", "addInQ"),
        ("Q", "sub", "x-y", "subInQ"),
        ("Q", "mul", "x*y", "mulInQ"),
        ("Q", "neg", "-x", "negInQ"),
        ("Q", "div", "x/y", "divInQ"),
        ("Q", "pow", "x^2", "powStructuralInQ"),
        ("R", "add", "x+y", "addInR"),
        ("R", "sub", "x-y", "subInR"),
        ("R", "mul", "x*y", "mulInR"),
        ("R", "neg", "-x", "negInR"),
        ("R", "div", "x/y", "divInR"),
        ("R", "pow", "x^2", "powStructuralInR"),
        ("C", "add", "x+y", "addInC"),
        ("C", "sub", "x-y", "subInC"),
        ("C", "mul", "x*y", "mulInC"),
        ("C", "neg", "-x", "negInC"),
        ("C", "div", "x/y", "divInC"),
        ("C", "pow", "x^2", "powStructuralInC"),
    ] {
        let parameters = if matches!(operation, "add" | "sub" | "mul" | "div") {
            "x,y"
        } else {
            "x"
        };
        let declaration_guard = if operation == "div" { ": y!=0" } else { "" };
        let declaration = format!(
            "have fn numeric_closure({parameters} {carrier}{declaration_guard}) {carrier}={expression}\n"
        );
        let tag = carrier.to_lowercase();
        let direct_x = format!("direct_{tag}_x");
        let direct_y = format!("direct_{tag}_y");
        let direct_expression = expression.replace('x', &direct_x).replace('y', &direct_y);
        let direct_guard = if matches!(carrier, "Q" | "R" | "C") {
            format!("{direct_y}!=0\n")
        } else {
            String::new()
        };
        let direct = format!(
            "have {direct_x} {carrier}\nhave {direct_y} {carrier}=2\n{direct_guard}{direct_expression} $in {carrier}\n"
        );
        let theorem = if operation == "div" {
            format!(
                "thm numeric_closure:\n    ? forall {parameters} {carrier}:\n        y!=0\n        =>:\n            {expression} $in {carrier}\n    {expression} $in {carrier}\n"
            )
        } else {
            format!(
                "thm numeric_closure:\n    ? forall {parameters} {carrier}:\n        {expression} $in {carrier}\n    {expression} $in {carrier}\n"
            )
        };
        for (context, source) in [
            ("declaration", declaration),
            ("direct", direct),
            ("theorem", theorem),
        ] {
            let (result, compiler) = super::execute(&source);
            let output = super::compile_run(&result, &compiler, "numeric_carrier_closure")
                .unwrap_or_else(|error| panic!("{carrier}/{operation}/{context}: {error}"));
            assert!(
                output.contains(&format!("Litex.{law}")),
                "{carrier}/{operation}/{context}"
            );
            assert!(!output.contains("sorry") && !output.contains("axiom"));
        }
    }
}

#[test]
fn numeric_closure_rejects_changed_binary_children_and_carriers() {
    for source in [
        "have fn numeric_product(x,y N) N=x*y\n",
        "have fn numeric_difference(x,y Z) Z=x-y\n",
    ] {
        for change in ["left", "right", "carrier"] {
            let (mut result, compiler) = super::execute(source);
            let proof = return_membership(&mut result.statement_results[0]);
            let (left, right) = match &mut proof.reason {
                StructuralMembershipReason::Mul { left, right }
                | StructuralMembershipReason::Sub { left, right } => (left, right),
                _ => panic!("the original structural binary operation"),
            };
            match change {
                "left" => left.element = super::number_object("23"),
                "right" => right.element = super::number_object("29"),
                "carrier" => left.set = StandardSet::C,
                _ => unreachable!(),
            }
            let error = super::compile_run(&result, &compiler, "changed_numeric_child")
                .expect_err("the carrier law cannot replace a corrupted source child");
            assert_eq!(error.route, "StructuralMembership/ArithmeticChild");
        }
    }
}

#[test]
fn natural_exponents_require_the_recorded_operand_and_carrier() {
    for source in ["have fn square(x N) N=x^2\n", "have fn square(x Z) Z=x^2\n"] {
        for change in ["base", "exponent", "carrier"] {
            let (mut result, compiler) = super::execute(source);
            let StructuralMembershipReason::Pow { base, exponent } =
                &mut return_membership(&mut result.statement_results[0]).reason
            else {
                panic!("the original structural power return");
            };
            match change {
                "base" => base.element = super::number_object("7"),
                "exponent" => exponent.element = super::number_object("3"),
                "carrier" => exponent.set = StandardSet::Z,
                _ => unreachable!(),
            }
            let error = super::compile_run(&result, &compiler, "changed_natural_power")
                .expect_err("a natural exponent cannot be replaced by another operand/carrier");
            assert_eq!(error.route, "StructuralMembership/PowChild");
        }
    }
}

const COORDINATE_SQUARE: &str = "forall a, b cart(R, R):\n    (b(1) - a(1))^2 $in C\n";

fn coordinate_square_membership(result: &mut RunLitexCodeResult) -> &mut StructuralMembershipProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
        &mut proof.searched_proof
    else {
        panic!("the original complex membership uses structural power closure");
    };
    proof
}

#[test]
fn coordinate_square_replays_its_structural_power_children() {
    let (mut result, compiler) = super::execute(COORDINATE_SQUARE);
    let proof = coordinate_square_membership(&mut result);
    assert_eq!(proof.set, StandardSet::C);
    let StructuralMembershipReason::Pow { base, exponent } = &proof.reason else {
        panic!("the original square certificate");
    };
    assert_eq!(base.set, StandardSet::C);
    assert_eq!(exponent.set, StandardSet::Z);
    assert!(matches!(
        base.reason,
        StructuralMembershipReason::Sub { .. }
    ));
    let output = super::compile_run(&result, &compiler, "coordinate_square")
        .expect("the original coordinate constructors and structural children compile");
    for (child, endpoint, carrier) in [("base", "base", "C"), ("exponent", "exponent", "Z")] {
        let inferred = output
            .find(&format!("have _elaborated_power_{child} :="))
            .expect("finish the original child proof before imposing the endpoint type");
        let checked = output
            .find(&format!(
                "have _recorded_power_{child} : Litex.In _litex_power.val.{endpoint} (Litex.{carrier} (M := M)) := _elaborated_power_{child}"
            ))
            .expect("the elaborated child must still match the exact owned endpoint and carrier");
        assert!(inferred < checked);
    }
}

#[test]
fn coordinate_square_rejects_changed_structural_children() {
    for change in ["base", "exponent", "carrier"] {
        let (mut result, compiler) = super::execute(COORDINATE_SQUARE);
        let StructuralMembershipReason::Pow { base, exponent } =
            &mut coordinate_square_membership(&mut result).reason
        else {
            panic!("the original square certificate");
        };
        match change {
            "base" => base.element = super::number_object("7"),
            "exponent" => exponent.element = super::number_object("3"),
            "carrier" => exponent.set = StandardSet::N,
            _ => unreachable!(),
        }
        let error = super::compile_run(&result, &compiler, "changed_coordinate_square")
            .expect_err("local type annotations cannot replace the selected child evidence");
        assert_eq!(error.route, "StructuralMembership/PowChild");
    }
}

#[test]
fn arithmetic_does_not_fabricate_natural_or_integer_membership() {
    for source in [
        "have fn numeric_difference(x,y N) N=x-y\n",
        "have fn opposite(x N) N=-x\n",
        "have fn half(x Z) Z=x/2\n",
        "have fn invalid(x R) R=x/0\n",
        "forall a, b cart(R, R):\n    (b(1) - a(1))^2 $in N\n",
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let result = runtime.run_litex_code(source).unwrap();
        assert!(
            !result.success,
            "invalid source membership must fail: {source}"
        );
        let compiler = super::LitexToLeanCompiler::new(runtime);
        assert_eq!(
            compiler
                .compile_run(&result, "invalid_numeric_closure")
                .unwrap_err()
                .route,
            "source_failed"
        );
    }
}

fn return_membership(statement: &mut ExecStmtResult) -> &mut StructuralMembershipProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(proof),
    )) = statement
    else {
        panic!("the original function declaration");
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = (&mut proof.anonymous_fn_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!("the original anonymous formula WD");
    };
    let AnonymousFnBodyInReturnSetProof::CheckedMembership(proof) = &mut proof.body_in_ret_set
    else {
        panic!("the original checked return membership");
    };
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
        &mut super::atomic_proof_mut(proof).searched_proof
    else {
        panic!("the original structural carrier proof");
    };
    proof
}
