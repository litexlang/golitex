use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const CASES: &[&str] = &[
    r#"# Repeatedly round down, starting at one half above a variable integer lower bound.
have fn rounded_sequence(n, b Z: n >= b) R by induc n from b:
    case n = b: 1 / 2
    case n > b: floor(rounded_sequence(n - 1, b))

rounded_sequence(0, 0) = 1 / 2
rounded_sequence(1, 0) = floor(rounded_sequence(0, 0)) = floor(1 / 2) = 0
"#,
    r#"# Repeatedly round up a real seed above a variable integer lower bound.
have fn ceiling_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 1 / 2
    case n > b: ceil(ceiling_steps(n - 1, b))

ceiling_steps(1, 0) = ceil(ceiling_steps(0, 0))
"#,
    r#"# Increment a sequence while keeping its values between zero and two.
have fn clamped_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: -1
    case n > b: max(min(clamped_steps(n - 1, b) + 1, 2), 0)

clamped_steps(1, 0) = max(min(clamped_steps(0, 0) + 1, 2), 0)
"#,
    r#"# Iterate the sign function on a real seed.
have fn sign_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: -2
    case n > b: sign(sign_steps(n - 1, b))

sign_steps(1, 0) = sign(sign_steps(0, 0))
"#,
    r#"# Iterate the square root of the absolute value of the preceding term.
have fn radical_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 4
    case n > b: sqrt(abs(radical_steps(n - 1, b)))

radical_steps(1, 0) = sqrt(abs(radical_steps(0, 0)))
"#,
    r#"# Iterate the base-two logarithm of the exponential of the preceding term.
have fn logarithmic_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 1
    case n > b: log(2, exp(logarithmic_steps(n - 1, b)))

logarithmic_steps(1, 0) = log(2, exp(logarithmic_steps(0, 0)))
"#,
    r#"# Iterate a composition of trigonometric and hyperbolic real functions.
have fn smooth_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 0
    case n > b: tanh(sinh(cosh(cos(sin(smooth_steps(n - 1, b))))))

smooth_steps(1, 0) = tanh(sinh(cosh(cos(sin(smooth_steps(0, 0))))))
"#,
    r#"# Iterate arctangent after arccotangent.
have fn angle_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 0
    case n > b: arctan(arccot(angle_steps(n - 1, b)))

angle_steps(1, 0) = arctan(arccot(angle_steps(0, 0)))
"#,
    r#"# Alternate a complex seed with its conjugate.
have fn conjugate_steps(n, b Z: n >= b) C by induc n from b:
    case n = b: i
    case n > b: conj(conjugate_steps(n - 1, b))

conjugate_steps(1, 0) = conj(conjugate_steps(0, 0))
"#,
    r#"# Iterate factorial on a natural-valued sequence.
have fn factorial_steps(n, b Z: n >= b) N by induc n from b:
    case n = b: 1
    case n > b: factorial(factorial_steps(n - 1, b))

factorial_steps(1, 0) = factorial(factorial_steps(0, 0))
"#,
    r#"# Replace an integer by its quotient and remainder on division by two.
have fn quotient_steps(n, b Z: n >= b) Z by induc n from b:
    case n = b: 13
    case n > b: quot(quotient_steps(n - 1, b), 2) + quotient_steps(n - 1, b) % 2

quotient_steps(1, 0) = quot(quotient_steps(0, 0), 2) + quotient_steps(0, 0) % 2
"#,
    r#"# Iterate gcd and lcm on natural numbers.
have fn divisor_steps(n, b Z: n >= b) N by induc n from b:
    case n = b: 6
    case n > b: gcd(lcm(divisor_steps(n - 1, b), 6), 4)

divisor_steps(1, 0) = gcd(lcm(divisor_steps(0, 0), 6), 4)
"#,
    r#"# Combine complex modulus and coordinates in a real-valued recurrence.
have fn complex_coordinate_steps(n, b Z: n >= b) R by induc n from b:
    case n = b: 1
    case n > b: C_abs(complex_coordinate_steps(n - 1, b)) + re(complex_coordinate_steps(n - 1, b)) + img(complex_coordinate_steps(n - 1, b))

complex_coordinate_steps(1, 0) = C_abs(complex_coordinate_steps(0, 0)) + re(complex_coordinate_steps(0, 0)) + img(complex_coordinate_steps(0, 0))
"#,
    r#"# Repeatedly transpose a square matrix.
have fn transpose_steps(n, b Z, A matrix(C,2,2): n >= b) matrix(C,2,2) by induc n from b:
    case n = b: A
    case n > b: transpose(transpose_steps(n - 1, b, A),2,2)

forall A matrix(C,2,2):
    transpose_steps(1, 0, A) = transpose(transpose_steps(0, 0, A), 2, 2)
"#,
    r#"# Repeatedly add a fixed rectangular matrix.
have fn rectangular_sum_steps(n, b Z, A matrix(C,2,3): n >= b) matrix(C,2,3) by induc n from b:
    case n = b: A
    case n > b: matrix_add(rectangular_sum_steps(n - 1, b, A), A, 2, 3)

forall A matrix(C,2,3):
    rectangular_sum_steps(1, 0, A) = matrix_add(rectangular_sum_steps(0, 0, A), A, 2, 3)
"#,
    r#"# Iterate floor while retaining a captured real seed.
template<seed R>:
    have fn rounded_from(n, b Z: n >= b) R by induc n from b:
        case n = b: seed
        case n > b: floor(rounded_from(n - 1, b))

\rounded_from<3 / 2>(1, 0) = floor(\rounded_from<3 / 2>(0, 0))
"#,
];

const NATURAL_CASES: &[&str] = &[
    r#"# Repeatedly round down, starting at one half.
have fn natural_rounding(n N) R by induc n from 0:
    case n = 0: 1 / 2
    case n > 0: floor(natural_rounding(n - 1))

natural_rounding(1) = floor(natural_rounding(0))
natural_rounding(0) = 1 / 2
floor(natural_rounding(0)) = floor(1 / 2) = 0
"#,
    r#"# Add two at each step and clamp the result to the interval from zero to three.
have fn natural_clamping(n N) R by induc n from 0:
    case n = 0: 1 / 2
    case n > 0: max(min(natural_clamping(n - 1) + 2, 3), 0)

natural_clamping(1) = max(min(natural_clamping(0) + 2, 3), 0)
"#,
    r#"# Iterate floor from a captured real seed using a natural index.
template<seed R>:
    have fn natural_floor_from(n N) R by induc n from 0:
        case n = 0: seed
        case n > 0: floor(natural_floor_from(n - 1))

\natural_floor_from<3 / 2>(1) = floor(\natural_floor_from<3 / 2>(0))
"#,
];

#[test]
fn recursive_constructor_catalog_replays_scalar_matrix_and_template_equations() {
    let mut failures = Vec::new();
    for source in CASES {
        let (run, compiler) = super::execute(source);
        let lean = match compiler.compile_run(&run, "recursive_constructors") {
            Ok(lean) => lean,
            Err(error) => {
                failures.push(format!("{source}: {error:?}"));
                continue;
            }
        };
        assert!(lean.contains("Litex.RecursiveFn M"));
        assert!(lean.contains("Litex.recursiveFn_equation"));
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "recursive_constructors")
                .unwrap()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

fn recursive(step: &mut ExecStmtResult) -> &mut ExecHaveFnByInducStmtSuccessResult {
    match step {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(body),
        )) => body,
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            crate::execute::ExecDefTemplateStmtResult::Success(template),
        )) => recursive(&mut template.body),
        _ => panic!("recursive definition"),
    }
}

#[test]
fn recursive_constructor_replay_requires_the_original_outer_and_smaller_call_wd() {
    for source in [CASES[0], CASES[15], NATURAL_CASES[0], NATURAL_CASES[2]] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let body = recursive(&mut run.statement_results[0]);
            let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } =
                &mut body.case_checks.cases[1].body
            else {
                panic!()
            };
            let Some(DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ArithmeticOperator(
                        ArithmeticOperatorObjWellDefinedProofByDef::Floor(floor),
                    ),
                ..
            }) = well_defined.as_detailed_success_mut().unwrap()
            else {
                panic!()
            };
            match mutation {
                0 => {
                    floor.requirement_fact_verified.clear();
                }
                1 => {
                    floor.child_obj_well_defined.clear();
                }
                _ => {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::FnObj(call),
                        ..
                    } = floor.child_obj_well_defined[0].as_detailed_mut().unwrap()
                    else {
                        panic!()
                    };
                    if mutation == 2 {
                        call.requirement_fact_verified.pop();
                    } else {
                        call.requirement_fact_verified.swap(0, 1);
                    }
                }
            }
            compiler
                .compile_run(&run, "changed_wd")
                .expect_err("constructor congruence cannot bypass original WD");
        }
    }
}

#[test]
fn recursive_matrix_constructor_preserves_distinct_dimension_wd_order() {
    let (mut run, compiler) = super::execute(CASES[14]);
    let body = recursive(&mut run.statement_results[0]);
    let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } =
        &mut body.case_checks.cases[1].body
    else {
        panic!()
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Add(add)),
        ..
    }) = well_defined.as_detailed_success_mut().unwrap()
    else {
        panic!()
    };
    add.child_obj_well_defined.swap(2, 3);
    compiler
        .compile_run(&run, "changed_dimension_order")
        .expect_err("original rows and columns are distinct");
}

#[test]
fn recursive_callee_constructor_and_numeric_observation_replay_the_original_branch() {
    check_callee_constructor(CASES[2], "RecursiveCallee.lean");
}

#[test]
fn natural_recursive_callee_replays_constructor_and_numeric_observation() {
    check_callee_constructor(NATURAL_CASES[1], "NaturalRecursiveCallee.lean");
}

fn check_callee_constructor(code: &str, filename: &str) {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(code);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[1]
    else {
        panic!()
    };
    let VerifyFactResult::Equality(verified) = &statement.verify_result else {
        panic!()
    };
    let VerifyEqualityResult::Success(verified) = verified.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByKnownForallFact(application) = &verified.searched_proof else {
        panic!()
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let caller = SourcePosition::new(
        Some(&root),
        SourceOwner::Verify(&statement.verify_result),
        1,
    );
    let Fact::ForallFact(source) = compiler
        .resolve_fact(application.detailed_ref().cite.fact_id, &caller)
        .unwrap()
    else {
        panic!()
    };
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equation)) =
        &source.then_facts[0]
    else {
        panic!()
    };
    let mut checked = String::new();
    for observe in [false, true] {
        let term = compiler
            .compile_recursive_callee_constructor(
                &source,
                0,
                &equation.right,
                application,
                &caller,
                observe,
            )
            .unwrap()
            .expect("exact recursive body constructor");
        assert!(term.contains("_prefix_returns"));
        assert!(term.contains("_constructor_equal"));
        checked.push_str(&format!("\nnoncomputable def replayed_body_{observe} := {term}\n#print axioms replayed_body_{observe}\n"));
    }
    if let Some(directory) = std::env::var_os("LITEX_LEAN_RECURSIVE_CONSTRUCTORS_OUTPUT") {
        let output = compiler
            .compile_run(&run, "recursive_callee_probe")
            .unwrap();
        let end = output.rfind("\nend ").unwrap();
        let output = format!("{}{}{}", &output[..end], checked, &output[end..]);
        std::fs::write(std::path::Path::new(&directory).join(filename), output).unwrap();
    }
}
