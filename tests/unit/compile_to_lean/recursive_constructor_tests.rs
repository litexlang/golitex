use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const CASES: &[&str] = &[
    include_str!("../../../lean/examples/recursive_rounding/statement.lit"),
    include_str!("../../../lean/examples/recursive_ceiling/statement.lit"),
    include_str!("../../../lean/examples/recursive_clamping/statement.lit"),
    include_str!("../../../lean/examples/recursive_sign/statement.lit"),
    include_str!("../../../lean/examples/recursive_radical/statement.lit"),
    include_str!("../../../lean/examples/recursive_logarithm/statement.lit"),
    include_str!("../../../lean/examples/recursive_smooth_composition/statement.lit"),
    include_str!("../../../lean/examples/recursive_angle_composition/statement.lit"),
    include_str!("../../../lean/examples/recursive_conjugate/statement.lit"),
    include_str!("../../../lean/examples/recursive_factorial/statement.lit"),
    include_str!("../../../lean/examples/recursive_integer_quotient/statement.lit"),
    include_str!("../../../lean/examples/recursive_common_divisor/statement.lit"),
    include_str!("../../../lean/examples/recursive_complex_coordinates/statement.lit"),
    include_str!("../../../lean/examples/recursive_matrix_transpose/statement.lit"),
    include_str!("../../../lean/examples/recursive_rectangular_sum/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_rounding/statement.lit"),
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
    for source in [CASES[0], CASES[15]] {
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
