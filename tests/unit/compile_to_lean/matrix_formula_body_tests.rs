use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionSpaceObjWellDefinedProofByDef, MatrixOperatorObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/matrix_formula_bodies/statement.lit");
const ZERO_SOURCE: &str =
    include_str!("../../../lean/examples/zero_matrix_formula_functions/statement.lit");
const SCALAR_SOURCES: &[(&str, &str)] = &[
    (
        include_str!("../../../lean/examples/matrix_trace_formula_functions/statement.lit"),
        "matrixTraceRawValue",
    ),
    (
        include_str!("../../../lean/examples/finite_inner_product_formula_functions/statement.lit"),
        "finiteInnerProductRawValue",
    ),
    (
        include_str!("../../../lean/examples/frobenius_norm_formula_functions/statement.lit"),
        "frobeniusNormRawSum",
    ),
];

const GRAPH_SOURCES: &[(&str, &str)] = &[
    (
        include_str!("../../../lean/examples/matrix_product_formula_functions/statement.lit"),
        "matrixMultiplyRawBody",
    ),
    (
        include_str!("../../../lean/examples/matrix_diagonal_formula_functions/statement.lit"),
        "matrixDiagonalBody",
    ),
    (
        include_str!("../../../lean/examples/matrix_outer_formula_functions/statement.lit"),
        "matrixOuterBody",
    ),
    (
        include_str!("../../../lean/examples/matrix_power_formula_functions/statement.lit"),
        "matrixPowerRawValue",
    ),
    (
        include_str!("../../../lean/examples/matrix_minor_formula_functions/statement.lit"),
        "matrixMinorBody",
    ),
    (
        include_str!("../../../lean/examples/matrix_adjugate_formula_functions/statement.lit"),
        "matrixCofactorRawValue",
    ),
    (
        include_str!("../../../lean/examples/matrix_inverse_formula_functions/statement.lit"),
        "M.divValue",
    ),
];

#[test]
fn matrix_graph_formula_bodies_preserve_shapes_and_original_beta() {
    for (source, denotation) in GRAPH_SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "matrix_graph_formula")
            .expect(denotation);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "matrix_graph_formula").unwrap()
        );
        assert!(lean.contains(denotation), "{denotation}");
    }
}

#[test]
fn matrix_graph_formula_bodies_reject_missing_or_reordered_wd() {
    for (source, _) in GRAPH_SOURCES {
        let declaration = source.lines().take(2).collect::<Vec<_>>().join("\n");
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(&declaration);
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                    ),
                ..
            } = formula(&mut run.statement_results[0])
                .anonymous_fn_well_defined
                .as_detailed_success_mut()
                .unwrap()
                .unwrap()
            else {
                panic!("original function WD");
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(body),
                ..
            } = literal.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("original matrix WD");
            };
            use MatrixOperatorObjWellDefinedProofByDef as W;
            let (children, requirements) = match body {
                W::Multiply(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Diagonal(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::OuterProduct(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Power(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Minor(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Adjugate(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Inverse(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("selected matrix construction"),
            };
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
                2 => children.swap(0, 1),
                _ => requirements.swap(0, 1),
            }
            compiler
                .compile_run(&run, "corrupted_matrix_graph")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn inverse_formula_body_requires_its_original_nonzero_citation() {
    let source =
        include_str!("../../../lean/examples/matrix_inverse_formula_functions/statement.lit");
    let declaration = source.lines().take(2).collect::<Vec<_>>().join("\n");
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(&declaration);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                ),
            ..
        } = formula(&mut run.statement_results[0])
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
            .unwrap()
        else {
            panic!("original function WD");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Inverse(inverse),
                ),
            ..
        } = literal.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("original inverse WD");
        };
        assert_eq!(inverse.requirement_fact_verified.len(), 3);
        match mutation {
            0 => {
                inverse.requirement_fact_verified.pop();
            }
            1 => inverse.requirement_fact_verified.swap(1, 2),
            _ => {
                let atom = super::atomic_proof_mut(&mut inverse.requirement_fact_verified[2]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut atom.searched_proof
                else {
                    panic!("original nonzero domain citation");
                };
                cite.cite_fact_id = FactId::new(u64::MAX);
            }
        }
        compiler
            .compile_run(&run, "bad_inverse_guard")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn empty_inverse_formula_rejects_corrupted_determinant_instantiation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
    let source =
        include_str!("../../../lean/examples/matrix_inverse_formula_functions/statement.lit");
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(source);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                ),
            ..
        } = formula(&mut run.statement_results[7])
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
            .unwrap()
        else {
            panic!("original empty function WD");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Inverse(inverse),
                ),
            ..
        } = literal.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("original empty inverse WD");
        };
        let atom = super::atomic_proof_mut(&mut inverse.requirement_fact_verified[2]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(citation) =
            &mut atom.searched_proof
        else {
            panic!("original universally proved nonzero determinant");
        };
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = citation.as_detailed_mut().unwrap().arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("original determinant structure");
        };
        assert!(matches!(
            pattern,
            Obj::MatrixOperator(MatrixOperator::Determinant(_))
        ));
        assert_eq!(child_matches.len(), 2);
        match mutation {
            0 => {
                child_matches.pop();
            }
            1 => child_matches.swap(0, 1),
            2 => *pattern = Obj::StandardSet(StandardSet::C),
            _ => *goal_arg = Obj::StandardSet(StandardSet::C),
        }
        compiler
            .compile_run(&run, "bad_determinant_instantiation")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn matrix_scalar_formula_bodies_preserve_captured_and_empty_dimensions() {
    for (source, denotation) in SCALAR_SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "matrix_scalar_formula").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "matrix_scalar_formula").unwrap()
        );
        assert!(lean.contains(denotation), "{denotation}");
    }
}

#[test]
fn matrix_scalar_formula_bodies_reject_changed_constructor_evidence() {
    for (source, _) in SCALAR_SOURCES {
        // Each pair starts with the constructor under test. The later beta
        // statements are covered by the complete-pair replay test above.
        let declaration = source.lines().take(2).collect::<Vec<_>>().join("\n");
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(&declaration);
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                    ),
                ..
            } = formula(&mut run.statement_results[0])
                .anonymous_fn_well_defined
                .as_detailed_success_mut()
                .unwrap()
                .unwrap()
            else {
                panic!("formula WD");
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(body),
                ..
            } = literal.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("matrix scalar WD");
            };
            use MatrixOperatorObjWellDefinedProofByDef as W;
            let (children, requirements) = match body {
                W::Trace(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::InnerProduct(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::FrobeniusNorm(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("selected matrix scalar"),
            };
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
                2 => children.swap(0, 1),
                3 => requirements.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&run, "changed_matrix_scalar").is_err(),
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn zero_matrix_formula_preserves_dimension_wd_and_return_membership() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(ZERO_SOURCE);
        if mutation == 0 {
            let lean = compiler.compile_run(&run, "zero_matrix_formulas").unwrap();
            assert_eq!(
                lean,
                compiler.compile_run(&run, "zero_matrix_formulas").unwrap()
            );
            assert!(lean.contains("Litex.zeroMatrix"));
            continue;
        }
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                ),
            ..
        } = formula(&mut run.statement_results[0])
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
            .unwrap()
        else {
            panic!("formula WD");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::ZeroMatrix(zero),
                ),
            ..
        } = literal.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("zero-matrix WD");
        };
        match mutation {
            1 => zero.child_obj_well_defined.clear(),
            2 => zero.requirement_fact_verified.clear(),
            3 => zero.child_obj_well_defined.swap(0, 1),
            4 => zero.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_zero_matrix").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn matrix_formula_bodies_replay_original_dimensions_and_carriers() {
    let (run, compiler) = super::execute(SOURCE);
    let lean = compiler.compile_run(&run, "matrix_formula_bodies").unwrap();
    assert_eq!(
        lean,
        compiler.compile_run(&run, "matrix_formula_bodies").unwrap()
    );
    for body in [
        "matrixTransposeBody",
        "matrixConjugateTransposeBody",
        "matrixEntrywiseBody",
        "matrixScaleBody",
    ] {
        assert!(lean.contains(body), "{body}");
    }
}

#[test]
fn nested_matrix_formula_reuses_completed_transpose_constructors() {
    let source = "have fn nested_transpose_4(A matrix(R,2,2)) matrix(R,2,2) = transpose(transpose(transpose(transpose(A,2,2),2,2),2,2),2,2)\n";
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "nested_transpose").unwrap();
    // Each layer has a source constructor. Its later membership and return
    // checks must reuse that value instead of reconstructing all inner layers.
    assert!(
        lean.matches("Litex.transpose ").count() <= 8,
        "duplicated matrix constructors"
    );
    assert!(
        lean.len() < 100_000,
        "nested proof unexpectedly expanded: {} bytes",
        lean.len()
    );
}

#[test]
fn matrix_formula_reuses_visible_signature_without_discarding_its_wd_checks() {
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixMembershipProof, MatrixSpaceMembershipEvidence,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;

    // Use the accepted real-transpose declaration from the canonical pair.
    let source = SOURCE.lines().take(2).collect::<Vec<_>>().join("\n");
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(&source);
        if mutation == 0 {
            let lean = compiler
                .compile_run(&run, "shared_matrix_signature")
                .unwrap();
            assert!(lean.contains("Litex.matrixSignature"));
            assert!(
                !lean.contains("_checked_header"),
                "repeated signature: {lean}"
            );
            continue;
        }
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                ),
            ..
        } = formula(&mut run.statement_results[0])
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
            .unwrap()
        else {
            panic!("formula WD");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Transpose(transpose),
                ),
            ..
        } = literal.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("transpose WD");
        };
        let VerifyFactResult::AtomicExceptEquality(member) =
            &mut transpose.requirement_fact_verified[2]
        else {
            panic!("complex matrix membership");
        };
        let VerifyAtomicExceptEqualityFactResult::Success(member) = member.as_mut() else {
            panic!("successful matrix membership");
        };
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Space(space)),
            ),
        ) = &mut member.searched_proof
        else {
            panic!("original matrix-space rule");
        };
        let MatrixSpaceMembershipEvidence::RealToComplex(real) = &mut space.membership else {
            panic!("original scalar widening");
        };
        let VerifyFactResult::AtomicExceptEquality(real) = real.as_mut() else {
            panic!("function-space membership");
        };
        let VerifyAtomicExceptEqualityFactResult::Success(real) = real.as_mut() else {
            panic!("successful real membership");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                    signature,
                )),
            ..
        } = real
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[1]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("independently checked signature");
        };
        match mutation {
            1 => signature.param_type_well_defined.clear(),
            2 => signature.defined_params.store_and_infer_results.clear(),
            3 => std::mem::swap(
                &mut signature.ret_set_well_defined,
                &mut signature.param_type_well_defined[0],
            ),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_shared_signature").is_err(),
            "the reused signature must still validate original WD mutation {mutation}"
        );
    }
}

fn formula(statement: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(proof),
    )) = statement
    else {
        panic!("source formula")
    };
    proof
}

#[test]
fn matrix_formula_bodies_cannot_replace_original_constructor_wd() {
    for index in 0..5 {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(SOURCE);
            let Some(DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(literal),
                    ),
                ..
            }) = formula(&mut run.statement_results[index])
                .anonymous_fn_well_defined
                .as_detailed_success_mut()
                .unwrap()
            else {
                panic!("formula WD")
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(body),
                ..
            } = literal.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("matrix body WD")
            };
            use MatrixOperatorObjWellDefinedProofByDef as W;
            let (children, requirements) = match body {
                W::Transpose(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::ConjugateTranspose(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Add(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Subtract(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::Scale(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("selected matrix operation"),
            };
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
                2 => children.swap(0, 1),
                3 => requirements.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&run, "bad_matrix_formula").is_err(),
                "operator {index}, mutation {mutation}"
            );
        }
    }
}

#[test]
fn matrix_scalar_empty_calculations_reject_corrupted_recorded_stages() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition;
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixDefinitionResidualProof, MatrixEqualityProof,
    };

    for (source, _) in SCALAR_SOURCES {
        // These two statements are the empty-dimension problem from the pair.
        let start = source.find("have fn empty_").unwrap();
        let end = source.find("have fn shifted_").unwrap();
        for mutation in 0..12 {
            let (mut run, compiler) = super::execute(&source[start..end]);
            let all = super::forall_proof_mut(&mut run.statement_results[1]);
            let equal = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
            let EqualFactSearchedProof::ByObjectDefinition(
                EqualitySearchProofByObjectDefinition::NativeMatrix(
                    MatrixEqualityProof::ScalarDefinition(definition),
                ),
            ) = &mut equal.searched_proof
            else {
                panic!("selected scalar definition");
            };
            let (functions, matrices, aggregates, left_value) = match definition.equality.as_mut() {
                MatrixDefinitionResidualProof::Verified(residual) => {
                    let equal = super::equality_proof_mut(residual);
                    let EqualFactSearchedProof::ByBuiltinRule(
                        EqualitySearchProofByBuiltinRule::AggregateCalculation(p),
                    ) = &mut equal.searched_proof
                    else {
                        panic!("selected aggregate calculation");
                    };
                    (
                        &mut p.function_evaluations,
                        &mut p.matrix_scalar_evaluations,
                        &mut p.aggregate_evaluations,
                        &mut p.left_value,
                    )
                }
                MatrixDefinitionResidualProof::ExactEvaluation(p) => (
                    &mut p.function_evaluations,
                    &mut p.matrix_scalar_evaluations,
                    &mut p.aggregate_evaluations,
                    &mut p.left_value,
                ),
                _ => panic!("recorded scalar calculation"),
            };
            assert_eq!(
                (functions.len(), matrices.len(), aggregates.len()),
                (1, 1, 2)
            );
            match mutation {
                0 => functions.clear(),
                1 => matrices.clear(),
                2 => aggregates.clear(),
                3 => matrices[0].source = super::number_object("0"),
                4 => matrices[0].expression = super::number_object("0"),
                5 => matrices[0].value = super::number_object("1"),
                6..=8 => {
                    let AggregateEvaluationResult::SumOfFiniteSet(p) = &mut aggregates[0] else {
                        panic!("empty finite sum");
                    };
                    match mutation {
                        6 => p.value = super::number_object("1"),
                        7 => p.enumeration.elements.push(super::number_object("1")),
                        _ => p.enumeration.resolved_set = super::number_object("0"),
                    }
                }
                9 => functions[0].nested_function_evidence.end += 1,
                10 => *left_value = super::number_object("1"),
                11 => {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::MatrixOperator(p),
                        ..
                    } = matrices[0].source_well_defined.as_detailed_mut().unwrap()
                    else {
                        panic!("original scalar WD");
                    };
                    use MatrixOperatorObjWellDefinedProofByDef as W;
                    match p {
                        W::Trace(p) => p.requirement_fact_verified.clear(),
                        W::InnerProduct(p) => p.requirement_fact_verified.clear(),
                        W::FrobeniusNorm(p) => p.requirement_fact_verified.clear(),
                        _ => panic!("selected scalar"),
                    }
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "corrupted_empty_scalar")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}
