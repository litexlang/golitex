use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::prelude::*;

const ADD: &str = include_str!("../../../lean/examples/native_matrix_trace_add/statement.lit");
const SCALE: &str = include_str!("../../../lean/examples/native_matrix_trace_scale/statement.lit");
const CYCLIC: &str =
    include_str!("../../../lean/examples/native_matrix_trace_cyclic/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_trace_reverse/statement.lit");
const ZERO: &str =
    include_str!("../../../lean/examples/native_matrix_trace_zero_order/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_trace_transport/statement.lit");
const LINEAR: &str = include_str!("../../../lean/examples/matrix_trace_linearity/statement.lit");
const EXPLICIT_CYCLIC: &str =
    include_str!("../../../lean/examples/matrix_trace_cyclic/statement.lit");

fn application(proof: &mut VerifyFactResult) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(proof);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual selected native trace law")
    };
    match law {
        NativeMatrixLawProof::TraceAdd(p) => &mut p.application,
        NativeMatrixLawProof::TraceScale(p) => &mut p.application,
        NativeMatrixLawProof::TraceCyclic(p) => &mut p.application,
        _ => panic!("actual trace variant"),
    }
}
fn selected(statement: &mut ExecStmtResult) -> &mut MatrixLawApplicationProof {
    application(&mut super::forall_proof_mut(statement).proved_then_facts[0].verify_result)
}
fn named_body(statement: &mut ExecStmtResult) -> &mut ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("named source theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall proof")
    };
    p
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let body = named_body(statement);
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("actual explicit theorem")
    };
    p
}

#[test]
fn native_trace_replays_original_schemas_repeated_premises_and_reverse_goals() {
    for (source, count) in [(ADD, 6), (SCALE, 4), (CYCLIC, 6), (ZERO, 6)] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0]);
        assert_eq!(p.requirements.len(), count);
        assert_eq!(p.requirement_proofs.len(), count);
        assert_ne!(p.requirements[0].fact_id(), p.requirements[1].fact_id());
        assert!(matches!(p.orientation, MatrixLawOrientation::Forward));
        super::compile_run(&run, &compiler, "native_trace").unwrap();
    }
    let (mut run, compiler) = super::execute(REVERSE);
    assert_eq!(run.statement_results.len(), 3);
    for (index, statement) in run.statement_results.iter_mut().enumerate() {
        let p = selected(statement);
        if index < 2 {
            assert!(matches!(p.orientation, MatrixLawOrientation::Reverse));
        } else {
            // Both cyclic endpoints are native candidates. The actual source
            // selects the left one forward, with the original arguments swapped.
            assert!(matches!(p.orientation, MatrixLawOrientation::Forward));
            assert!(
                matches!(&p.arguments[0], Obj::Identifier(IdentifierObj::Plain { name, .. }) if name == "replay_trace_B")
            );
            assert!(
                matches!(&p.arguments[1], Obj::Identifier(IdentifierObj::Plain { name, .. }) if name == "replay_trace_A")
            );
        }
    }
    super::compile_run(&run, &compiler, "reverse_trace").unwrap();
}

#[test]
fn native_trace_requires_exact_requirement_count_order_identity_and_carriers() {
    for source in [ADD, SCALE, CYCLIC] {
        for change in ["count", "extra", "order", "id", "carrier"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "count" => {
                    p.requirement_proofs.pop();
                }
                "extra" => p.requirements.push(p.requirements[0].clone()),
                "order" => p.requirement_proofs.swap(0, 1),
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0] else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_trace_keeps_original_arguments_conclusion_operation_and_orientation() {
    for source in [ADD, SCALE, CYCLIC] {
        for change in ["argument", "conclusion", "order", "orientation"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "conclusion" => p.conclusion.right = super::number_object("7"),
                "order" => {
                    let Obj::MatrixOperator(MatrixOperator::Trace(t)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    t.order = Box::new(super::number_object("7"));
                }
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_trace_cyclic_preserves_each_rectangular_product_dimension() {
    for field in ["rows", "inner", "cols"] {
        let (mut run, compiler) = super::execute(CYCLIC);
        let p = selected(&mut run.statement_results[0]);
        let Obj::MatrixOperator(MatrixOperator::Trace(t)) = &mut p.conclusion.right else {
            panic!()
        };
        let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = t.matrix.as_mut() else {
            panic!()
        };
        match field {
            "rows" => m.rows = m.inner.clone(),
            "inner" => m.inner = m.cols.clone(),
            "cols" => m.cols = m.inner.clone(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, field).is_err());
    }
}

#[test]
fn explicit_trace_replays_all_original_clauses_stores_and_named_rectangular_call() {
    for source in [LINEAR, EXPLICIT_CYCLIC] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        let expected = if source == LINEAR { 7 } else { 6 };
        assert_eq!(p.dom_proofs.len(), expected);
        assert_eq!(p.dom_stores.len(), expected);
        assert_eq!(
            p.builtin.as_ref().unwrap().conclusions.len(),
            if source == LINEAR { 2 } else { 1 }
        );
        super::compile_run(&run, &compiler, "explicit_trace").unwrap();
    }
}

#[test]
fn explicit_trace_rejects_missing_reordered_and_changed_original_stages() {
    for source in [LINEAR, EXPLICIT_CYCLIC] {
        for change in ["stores", "proof_order", "clause", "wd", "id", "argument"] {
            let (mut run, compiler) = super::execute(source);
            let p = release(&mut run.statement_results[0]);
            match change {
                "stores" => {
                    p.dom_stores.pop();
                }
                "proof_order" => p.dom_proofs.swap(0, 1),
                "clause" => {
                    p.builtin.as_mut().unwrap().conclusions.pop();
                }
                "wd" => {
                    p.conclusions_wd.pop();
                }
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn explicit_trace_linearity_cannot_replace_its_two_distinct_clauses() {
    let (mut run, compiler) = super::execute(LINEAR);
    release(&mut run.statement_results[0])
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    assert!(super::compile_run(&run, &compiler, "wrong_trace_clauses").is_err());
}

#[test]
fn native_trace_endpoint_transport_keeps_the_original_stored_equality_path() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    let body = named_body(&mut run.statement_results[0]);
    let stored = super::fact_statement_mut(&mut body.proof_steps[0])
        .store_and_infer_result
        .primary_fact_id();
    let p = application(&mut body.conclusion_proofs[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_ref()
    else {
        panic!("actual stored endpoint equality")
    };
    assert_eq!(path.path[0].2, stored);
    super::compile_run(&run, &compiler, "transport_trace").unwrap();
    let p = application(&mut named_body(&mut run.statement_results[0]).conclusion_proofs[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_trace_transport").is_err());
}

#[test]
fn square_matrix_scalar_normalization_replays_existing_constructor_wd_and_codomain() {
    for op in ["trace", "det"] {
        let source = format!(
            "forall n N, A, B matrix(C,n,n):\n    {op}(A,n) + {op}(B,n) = {op}(B,n) + {op}(A,n)\n"
        );
        let (mut run, compiler) = super::execute(&source);
        let eq = super::equality_proof_mut(
            &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                .verify_result,
        );
        assert!(matches!(
            eq.searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
                EqualitySearchProofByCalculation::Rational { .. }
            ))
        ));
        let output = super::compile_run(&run, &compiler, "square_scalar_normalization").unwrap();
        assert!(output.contains(if op == "trace" {
            "matrixTraceInC"
        } else {
            "matrixDeterminantInC"
        }));
    }
}

#[test]
fn square_matrix_scalar_observation_cannot_replace_missing_original_wd_requirements() {
    for op in ["trace", "det"] {
        let source = format!(
            "forall n N, A, B matrix(C,n,n):\n    {op}(A,n) + {op}(B,n) = {op}(B,n) + {op}(A,n)\n"
        );
        let (mut run, compiler) = super::execute(&source);
        let eq = super::equality_proof_mut(
            &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                .verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Add(sum),
                ),
            ..
        } = eq
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("original sum formation")
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(matrix),
            ..
        } = sum.child_obj_well_defined[0].as_detailed_mut().unwrap()
        else {
            panic!("original scalar constructor")
        };
        match matrix {
            MatrixOperatorObjWellDefinedProofByDef::Trace(p) => {
                p.requirement_fact_verified.pop();
            }
            MatrixOperatorObjWellDefinedProofByDef::Determinant(p) => {
                p.requirement_fact_verified.pop();
            }
            _ => panic!("original square matrix scalar"),
        }
        assert!(super::compile_run(&run, &compiler, "missing_square_scalar_wd").is_err());
    }
}
