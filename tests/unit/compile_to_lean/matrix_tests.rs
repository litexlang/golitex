use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByObjectDefinition;
use crate::prelude::*;

#[test]
fn matrix_ranks_replay_membership_laws_aliases_and_functions() {
    for source in [
        include_str!("../../../lean/examples/matrix_rank_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_bounds/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_zero/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_identity/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_alias/statement.lit"),
        include_str!("../../../lean/examples/matrix_rank_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_ranks")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_ranks_reject_missing_reordered_and_changed_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..4 {
        let (mut run, compiler) =
            super::execute("forall m,n N,A matrix(C,m,n):\n    $is_set(matrix_rank(A,m,n))");
        compiler.compile_run(&run, "valid_rank_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Rank(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("rank WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 1),
            2 => p.child_obj_well_defined.swap(0, 1),
            _ => {
                let AtomicFact::InFact(f) =
                    &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[2]).fact
                else {
                    panic!("matrix domain")
                };
                let Obj::SetFormer(SetFormer::MatrixSet(m)) = &mut f.set else {
                    panic!("matrix set")
                };
                std::mem::swap(&mut m.rows, &mut m.cols);
            }
        }
        assert!(compiler.compile_run(&run, "changed_rank_wd").is_err());
    }
}

#[test]
fn matrix_ranks_reject_changed_theorem_contracts() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    for source in [
        "release thm matrix_rank_bounds(zero_matrix(2,3),2,3)",
        "release thm matrix_rank_zero(2,3)",
        "release thm matrix_rank_identity(2)",
    ] {
        for changed in 0..4 {
            let (mut run, compiler) = super::execute(source);
            compiler.compile_run(&run, "valid_rank_law").unwrap();
            let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) = &mut run.statement_results[0]
            else {
                panic!("rank release")
            };
            match changed {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.conclusions_wd.clear(),
                2 => match &mut p.builtin.as_mut().unwrap().conclusions[0] {
                    Fact::AtomicFact(AtomicFact::InFact(f)) => {
                        f.set = Obj::StandardSet(StandardSet::R)
                    }
                    Fact::AtomicFact(AtomicFact::EqualFact(f)) => {
                        f.right = Obj::Literal(Literal::Number(Number::new("7".into())))
                    }
                    _ => panic!("rank conclusion"),
                },
                _ => p.dom_stores.clear(),
            }
            assert!(compiler.compile_run(&run, "changed_rank_law").is_err());
        }
    }
}

#[test]
fn matrix_ranks_reject_invalid_domains_and_unproved_positive_rank() {
    for source in [
        "$is_set(matrix_rank(zero_matrix(2,3),2,2))",
        "$is_set(matrix_rank(zero_matrix(2,3),-1,3))",
        "forall A set:\n    $is_set(matrix_rank(A,2,3))",
        "matrix_rank(zero_matrix(2,3),2,3) $in N+",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_rank_domain")
            .is_err());
    }
}

#[test]
fn matrix_ranks_reject_missing_or_reordered_alias_congruence() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/matrix_rank_alias/statement.lit"
        ));
        compiler.compile_run(&run, "valid_rank_alias").unwrap();
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[4]).verify_result,
        );
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::ViaPeers(p),
        ) = &mut equality.searched_proof
        else {
            panic!("stored equality bridge")
        };
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = p.bridge.searched_proof.as_mut()
        else {
            panic!("rank congruence")
        };
        if missing {
            p.corresponding_arg_equal_proofs.pop();
        } else {
            p.corresponding_arg_equal_proofs.swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "changed_rank_alias").is_err());
    }
}

#[test]
fn matrix_exact_determinants_reject_changed_function_evaluations() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::FunctionApplicationExpansionProof;
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixDefinitionResidualProof, MatrixEqualityProof,
    };
    for changed in 0..7 {
        let (mut run, compiler) = super::execute("det(identity_matrix(2),2) = 1");
        compiler
            .compile_run(&run, "valid_exact_determinant")
            .unwrap();
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::NativeMatrix(
                MatrixEqualityProof::ScalarDefinition(p),
            ),
        ) = &mut equality.searched_proof
        else {
            panic!("determinant definition")
        };
        let MatrixDefinitionResidualProof::ExactEvaluation(e) = p.equality.as_mut() else {
            panic!("exact evaluation")
        };
        assert_eq!(e.function_evaluations.len(), 4);
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        match changed {
            0 => {
                e.function_evaluations.pop();
            }
            1 => e.function_evaluations.swap(0, 1),
            2 => e.function_evaluations[0].value = zero,
            3 => e.left_value = zero,
            4 => e.right_value = zero,
            5 => {
                let FunctionApplicationExpansionProof::CheckedBeta(beta) =
                    &mut e.function_evaluations[0].expansion
                else {
                    panic!("native beta")
                };
                beta.expanded_body = zero;
            }
            _ => {
                let first = e.function_evaluations.remove(0);
                e.function_evaluations.push(first);
            }
        }
        assert!(compiler
            .compile_run(&run, "changed_exact_determinant")
            .is_err());
    }
}

#[test]
fn matrix_inverses_replay_guarded_carriers_coordinates_and_definition() {
    for source in [
        include_str!("../../../lean/examples/matrix_inverse_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_real_values/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_two_steps/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_theorem/statement.lit"),
        include_str!("../../../lean/examples/matrix_inverse_alias/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_inverses")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_inverses_reject_missing_reordered_or_changed_determinant_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..5 {
        let (mut run, compiler) = super::execute("forall n N, A matrix(C,n,n):\n    det(A,n) != 0\n    =>:\n        $is_set(matrix_inverse(A,n))");
        compiler.compile_run(&run, "valid_inverse_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Inverse(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("inverse WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(1, 2),
            2 => p.child_obj_well_defined.swap(0, 1),
            _ => {
                let AtomicFact::NotEqualFact(f) =
                    &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[2]).fact
                else {
                    panic!("nonzero determinant")
                };
                if changed == 3 {
                    f.right = Obj::Literal(Literal::Number(Number::new("1".into())));
                } else {
                    let Obj::MatrixOperator(MatrixOperator::Determinant(d)) = &mut f.left else {
                        panic!("determinant")
                    };
                    d.order = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
                }
            }
        }
        assert!(compiler.compile_run(&run, "bad_inverse_wd").is_err());
    }
}

#[test]
fn matrix_inverses_reject_wrong_quotient_and_real_carrier_evidence() {
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof,MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for changed in 0..5 {
        let (mut run, compiler) = super::execute("forall n N, A matrix(R,n,n):\n    det(A,n) != 0\n    =>:\n        matrix_inverse(A,n) $in matrix(R,n,n)");
        compiler.compile_run(&run, "valid_inverse_formula").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("inverse callable")
        };
        match changed {
            0 | 1 => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) =
                    p.callable.function.equal_to.as_mut()
                else {
                    panic!("inverse quotient")
                };
                if changed == 0 {
                    d.right = Box::new(Obj::Literal(Literal::Number(Number::new("1".into()))));
                } else {
                    let Obj::MatrixOperator(MatrixOperator::Cofactor(c)) = d.left.as_mut() else {
                        panic!("inverse cofactor")
                    };
                    std::mem::swap(&mut c.row, &mut c.col);
                }
            }
            2 => {
                let MatrixFunctionScalarCarrierProof::RealOperands(operands) =
                    &mut p.callable.scalar_carrier
                else {
                    panic!("inverse real evidence")
                };
                operands.clear();
            }
            3 => p.callable.scalar_carrier = MatrixFunctionScalarCarrierProof::ComplexInput,
            _ => {
                p.callable.function.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
        }
        assert!(compiler.compile_run(&run, "bad_inverse_formula").is_err());
    }
}

#[test]
fn matrix_inverses_reject_missing_guard_zero_determinant_and_wrong_shapes() {
    for source in [
        "forall n N, A matrix(C,n,n):\n    $is_set(matrix_inverse(A,n))",
        "$is_set(matrix_inverse(zero_matrix(2,2),2))",
        "$is_set(matrix_inverse(zero_matrix(2,3),2))",
        "$is_set(matrix_inverse(identity_matrix(2),-1))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_inverse_domain")
            .is_err());
    }
}

#[test]
fn matrix_adjugates_replay_carriers_coordinates_empty_and_definition() {
    for source in [
        include_str!("../../../lean/examples/matrix_adjugate_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_alias/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_theorem/statement.lit"),
        include_str!("../../../lean/examples/matrix_adjugate_two_steps/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_adjugates")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_adjugates_reject_missing_reordered_or_changed_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..3 {
        let (mut run, compiler) =
            super::execute("forall n N, A matrix(C,n,n):\n    $is_set(matrix_adjugate(A,n))");
        compiler.compile_run(&run, "valid_adjugate_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Adjugate(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("adjugate WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 1),
            _ => p.child_obj_well_defined.swap(0, 1),
        }
        assert!(compiler.compile_run(&run, "bad_adjugate_wd").is_err());
    }
}

#[test]
fn matrix_adjugates_reject_untransposed_cofactor_and_wrong_carrier() {
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof,MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for changed in 0..4 {
        let (mut run, compiler) = super::execute(
            "forall n N, A matrix(R,n,n):\n    matrix_adjugate(A,n) $in matrix(R,n,n)",
        );
        compiler
            .compile_run(&run, "valid_adjugate_formula")
            .unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("adjugate callable")
        };
        match changed {
            0 => {
                let Obj::MatrixOperator(MatrixOperator::Cofactor(c)) =
                    p.callable.function.equal_to.as_mut()
                else {
                    panic!("adjugate cofactor")
                };
                std::mem::swap(&mut c.row, &mut c.col);
            }
            1 => {
                let MatrixFunctionScalarCarrierProof::RealOperands(operands) =
                    &mut p.callable.scalar_carrier
                else {
                    panic!("adjugate real evidence")
                };
                operands.clear();
            }
            2 => p.callable.scalar_carrier = MatrixFunctionScalarCarrierProof::ComplexInput,
            _ => {
                p.callable.function.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
        }
        assert!(compiler.compile_run(&run, "bad_adjugate_formula").is_err());
    }
}

#[test]
fn matrix_adjugates_reject_negative_nonsquare_and_outside_indices() {
    for source in [
        "$is_set(matrix_adjugate(zero_matrix(2,2),-1))",
        "$is_set(matrix_adjugate(zero_matrix(2,3),2))",
        "$is_set(matrix_adjugate(zero_matrix(0,0),0)(1,1))",
        "$is_set(matrix_adjugate(zero_matrix(2,2),2)(3,1))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_adjugate_domain")
            .is_err());
    }
}

#[test]
fn matrix_cofactors_replay_carriers_small_orders_and_references() {
    for source in [
        include_str!("../../../lean/examples/matrix_cofactor_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_cofactor_small_orders/statement.lit"),
        include_str!("../../../lean/examples/matrix_cofactor_alias/statement.lit"),
        include_str!("../../../lean/examples/matrix_cofactor_theorem/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_cofactors")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_cofactors_reject_missing_reordered_and_misassigned_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..4 {
        let (mut run, compiler) = super::execute(
            "forall n N+, A matrix(C,n,n), r,c closed_range(1,n):\n    $is_set(matrix_cofactor(A,n,r,c))",
        );
        compiler.compile_run(&run, "valid_cofactor_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Cofactor(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("cofactor WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 3),
            2 => p.requirement_fact_verified.swap(1, 2),
            _ => p.child_obj_well_defined.swap(2, 3),
        }
        assert!(compiler.compile_run(&run, "bad_cofactor_wd").is_err());
    }
}

#[test]
fn matrix_cofactors_reject_missing_or_misclassified_real_evidence() {
    use crate::execute::execute_fact_stmt::matrix_operations::{ExtendedMatrixScalarMembershipProof, MatrixScalarCarrierProof};
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for missing in [true, false] {
        let (mut run, compiler) = super::execute(
            "forall n N+, A matrix(R,n,n), r,c closed_range(1,n):\n    matrix_cofactor(A,n,r,c) $in R",
        );
        compiler.compile_run(&run, "valid_cofactor_real").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(
                    MatrixMembershipProof::ExtendedScalar(
                        ExtendedMatrixScalarMembershipProof::Cofactor(p),
                    ),
                ),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("cofactor real carrier")
        };
        if missing {
            let MatrixScalarCarrierProof::RealInputs(operands) = &mut p.carrier else {
                panic!("real operand")
            };
            operands.clear();
        } else {
            p.carrier = MatrixScalarCarrierProof::StandardSubset;
        }
        assert!(compiler.compile_run(&run, "bad_cofactor_real").is_err());
    }
}

#[test]
fn matrix_cofactors_reject_changed_expansion_and_invalid_domains() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) =
        super::execute("forall A matrix(C,2,2):\n    matrix_cofactor(A,2,1,2) = -A(2,1)");
    compiler
        .compile_run(&run, "valid_cofactor_expansion")
        .unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let eq = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(MatrixEqualityProof::ScalarDefinition(
            p,
        )),
    ) = &mut eq.searched_proof
    else {
        panic!("cofactor expansion")
    };
    p.expression = Obj::Literal(Literal::Number(Number::new("0".into())));
    assert!(compiler
        .compile_run(&run, "bad_cofactor_expansion")
        .is_err());
    for source in [
        "forall A matrix(C,0,0):\n    $is_set(matrix_cofactor(A,0,1,1))",
        "forall A matrix(C,2,2):\n    $is_set(matrix_cofactor(A,2,0,1))",
        "forall A matrix(C,2,2):\n    $is_set(matrix_cofactor(A,2,1,3))",
        "forall A matrix(C,2,3):\n    $is_set(matrix_cofactor(A,2,1,1))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_cofactor_domain")
            .is_err());
    }
}

#[test]
fn matrix_minors_replay_domains_and_coordinates() {
    for source in [
        include_str!("../../../lean/examples/matrix_minor_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_minor_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_minor_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_minor_theorem/statement.lit"),
        include_str!("../../../lean/examples/matrix_minor_alias/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_minors")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_minors_reject_missing_reordered_and_misassigned_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..4 {
        let (mut run, compiler) = super::execute(
            "forall n N+, A matrix(C,n,n), r,c closed_range(1,n):\n    $is_set(matrix_minor(A,n,r,c))",
        );
        compiler.compile_run(&run, "valid_minor_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Minor(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("minor WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 3),
            2 => p.requirement_fact_verified.swap(1, 2),
            _ => p.child_obj_well_defined.swap(2, 3),
        }
        assert!(compiler.compile_run(&run, "bad_minor_wd").is_err());
    }
}

#[test]
fn matrix_minors_reject_changed_callable_formula() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for changed in 0..3 {
        let (mut run, compiler) = super::execute(
            "forall n N+, A matrix(C,n,n), r,c closed_range(1,n):\n    matrix_minor(A,n,r,c) $in matrix(C,n-1,n-1)",
        );
        compiler.compile_run(&run, "valid_minor_formula").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("minor callable")
        };
        let MatrixOperator::Minor(m) = &mut p.callable.operator else {
            panic!("minor")
        };
        match changed {
            0 => {
                p.callable.function.equal_to =
                    Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))))
            }
            1 => std::mem::swap(&mut m.row, &mut m.col),
            _ => {
                p.callable.function.body.set_bound_parameters.groups[0].param_type = m.order.clone()
            }
        }
        assert!(compiler.compile_run(&run, "bad_minor_formula").is_err());
    }
}

#[test]
fn matrix_minors_reject_invalid_domains() {
    for source in [
        "forall A matrix(C,0,0):\n    $is_set(matrix_minor(A,0,1,1))",
        "forall A matrix(C,2,2):\n    $is_set(matrix_minor(A,2,0,1))",
        "forall A matrix(C,2,2):\n    $is_set(matrix_minor(A,2,1,3))",
        "forall A matrix(C,2,3):\n    $is_set(matrix_minor(A,2,1,1))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_minor_domain")
            .is_err());
    }
}

#[test]
fn matrix_powers_replay_domains_and_selected_theorems() {
    for source in [
        include_str!("../../../lean/examples/matrix_power_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_literal/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_alias/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_zero/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_successor/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_powers")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_powers_reject_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..3 {
        let (mut run, compiler) =
            super::execute("forall n,p N,A matrix(C,n,n):\n    $is_set(matrix_power(A,n,p))");
        compiler.compile_run(&run, "valid_power_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Power(p)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("power WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 1),
            _ => p.child_obj_well_defined.swap(1, 2),
        }
        assert!(compiler.compile_run(&run, "bad_power_wd").is_err());
    }
}

#[test]
fn matrix_powers_reject_changed_callable_formula() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for (exponent, changed) in [("0", 0), ("2", 0), ("p", 0), ("p", 1), ("p", 2)] {
        let source = format!(
            "forall n,p N,A matrix(C,n,n):\n    matrix_power(A,n,{exponent}) $in matrix(C,n,n)"
        );
        let (mut run, compiler) = super::execute(&source);
        compiler.compile_run(&run, "valid_power_formula").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("power callable")
        };
        if changed == 0 {
            p.callable.function.equal_to =
                Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        } else {
            let Obj::FnObj(call) = p.callable.function.equal_to.as_mut() else {
                panic!("fold call")
            };
            let FnObjHead::Object(head) = call.head.as_mut() else {
                panic!("fold head")
            };
            let Obj::IteratedOperator(IteratedOperator::Reduce(fold)) = head.as_mut() else {
                panic!("power fold")
            };
            if changed == 1 {
                let MatrixOperator::Power(power) = &p.callable.operator else {
                    panic!("power")
                };
                fold.end = power.order.clone();
            } else {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(op)) = fold.op.as_mut() else {
                    panic!("fold operation")
                };
                let Obj::MatrixOperator(MatrixOperator::Multiply(product)) = op.equal_to.as_mut()
                else {
                    panic!("fold product")
                };
                std::mem::swap(&mut product.left, &mut product.right);
            }
        }
        assert!(compiler.compile_run(&run, "bad_power_formula").is_err());
    }
}

#[test]
fn matrix_powers_reject_changed_theorem_and_invalid_domains() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    for source in [
        include_str!("../../../lean/examples/matrix_power_zero/statement.lit"),
        include_str!("../../../lean/examples/matrix_power_successor/statement.lit"),
    ] {
        for changed in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(thm),
            )) = &mut run.statement_results[0]
            else {
                panic!("power theorem")
            };
            let ExecDefThmBodyProof::Forall(body) = &mut thm.body else {
                panic!("power forall")
            };
            let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) = &mut body.proof_steps[0]
            else {
                panic!("power release")
            };
            match changed {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.conclusions_wd.clear(),
                _ => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
                        &mut p.builtin.as_mut().unwrap().conclusions[0]
                    else {
                        panic!("power conclusion")
                    };
                    f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
            }
            assert!(compiler.compile_run(&run, "bad_power_theorem").is_err());
        }
    }
    for source in [
        "forall A matrix(C,2,2):\n    $is_set(matrix_power(A,2,-1))",
        "forall A matrix(C,2,2):\n    $is_set(matrix_power(A,2,1/2))",
        "forall A matrix(C,2,3):\n    $is_set(matrix_power(A,2,2))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_power_domain")
            .is_err());
    }
}

#[test]
fn matrix_determinants_replay_original_domains_and_laws() {
    for source in [
        include_str!("../../../lean/examples/matrix_determinant/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_identity/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_transpose/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_adjoint/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_small_orders/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_determinants")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_determinants_reject_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for changed in 0..3 {
        let (mut run, compiler) =
            super::execute("forall n N, A matrix(C,n,n):\n    $is_set(det(A,n))");
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::MatrixOperator(W::Determinant(p)),
            ..
        } = &mut proof.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("determinant WD")
        };
        match changed {
            0 => {
                p.requirement_fact_verified.pop();
            }
            1 => p.requirement_fact_verified.swap(0, 1),
            _ => p.child_obj_well_defined.swap(0, 1),
        }
        assert!(compiler.compile_run(&run, "bad_det_wd").is_err());
    }
}

#[test]
fn matrix_determinants_reject_changed_builtin_contracts() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    for source in [
        include_str!("../../../lean/examples/matrix_determinant_identity/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_transpose/statement.lit"),
        include_str!("../../../lean/examples/matrix_determinant_adjoint/statement.lit"),
    ] {
        for changed in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(thm),
            )) = &mut run.statement_results[0]
            else {
                panic!("det theorem")
            };
            let ExecDefThmBodyProof::Forall(body) = &mut thm.body else {
                panic!("det forall")
            };
            let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) = &mut body.proof_steps[0]
            else {
                panic!("det release")
            };
            match changed {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => {
                    p.conclusions_wd.clear();
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
                        &mut p.builtin.as_mut().unwrap().conclusions[0]
                    else {
                        panic!("det conclusion")
                    };
                    f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
            }
            assert!(compiler.compile_run(&run, "bad_det_theorem").is_err());
        }
    }
}

#[test]
fn matrix_determinants_reject_changed_expansion_and_invalid_domain() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) =
        super::execute("forall A matrix(C,2,2):\n    det(A,2)=A(1,1)*A(2,2)-A(1,2)*A(2,1)");
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let proof = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(MatrixEqualityProof::ScalarDefinition(
            p,
        )),
    ) = &mut proof.searched_proof
    else {
        panic!("det expansion")
    };
    p.expression = Obj::Literal(Literal::Number(Number::new("0".into())));
    assert!(compiler.compile_run(&run, "bad_det_expansion").is_err());
    for source in [
        "forall A matrix(C,2,3):\n    $is_set(det(A,2))",
        "forall A set:\n    $is_set(det(A,2))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_det_domain")
            .is_err());
    }
}

#[test]
fn matrix_norms_replay_original_wd_and_square_theorems() {
    for source in [
        include_str!("../../../lean/examples/euclidean_norm_definition/statement.lit"),
        include_str!("../../../lean/examples/frobenius_norm_definition/statement.lit"),
        include_str!("../../../lean/examples/euclidean_norm/statement.lit"),
        include_str!("../../../lean/examples/frobenius_norm/statement.lit"),
        include_str!("../../../lean/examples/euclidean_norm_nonnegative/statement.lit"),
        include_str!("../../../lean/examples/frobenius_norm_nonnegative/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "matrix_norms")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn matrix_norms_reject_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef as W;
    for source in [
        "forall n N, v cart_n(C,n):\n    $is_set(euclidean_norm(v,n))",
        "forall m,n N, A matrix(C,m,n):\n    $is_set(frobenius_norm(A,m,n))",
    ] {
        for changed in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let proof = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
            let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(wd),
                ..
            } = &mut proof.well_defined_proof.well_defined_of_each_parameter[0]
            else {
                panic!("norm WD")
            };
            let (children, requirements) = match wd {
                W::EuclideanNorm(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                W::FrobeniusNorm(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("norm WD variant"),
            };
            match changed {
                0 => {
                    requirements.pop();
                }
                1 => requirements.swap(0, 1),
                _ => children.swap(0, 1),
            }
            assert!(
                compiler.compile_run(&run, "bad_norm_wd").is_err(),
                "case {changed}"
            );
        }
    }
}

#[test]
fn matrix_norms_reject_changed_builtin_certificate() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    for source in [
        include_str!("../../../lean/examples/euclidean_norm_nonnegative/statement.lit"),
        include_str!("../../../lean/examples/frobenius_norm_nonnegative/statement.lit"),
    ] {
        for changed in 0..5 {
            let (mut run, compiler) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(theorem),
            )) = &mut run.statement_results[0]
            else {
                panic!("norm theorem")
            };
            let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
                panic!("norm theorem body")
            };
            let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                ExecReleaseThmStmtResult::Success(p),
            )) = &mut body.proof_steps[0]
            else {
                panic!("norm theorem")
            };
            match changed {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_proofs.swap(0, 1),
                2 => {
                    p.conclusions_wd.pop();
                }
                3 => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
                        &mut p.builtin.as_mut().unwrap().conclusions[0]
                    else {
                        panic!("square conclusion")
                    };
                    f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
                _ => p.builtin.as_mut().unwrap().conclusions.swap(0, 1),
            }
            assert!(
                compiler.compile_run(&run, "bad_norm_square").is_err(),
                "case {changed}"
            );
        }
    }
}

#[test]
fn matrix_norms_reject_wrong_dimensions_and_missing_input_carriers() {
    for source in [
        "forall v cart_n(C,2):\n    $is_set(euclidean_norm(v,3))",
        "forall A matrix(C,2,3):\n    $is_set(frobenius_norm(A,3,2))",
        "forall v set:\n    $is_set(euclidean_norm(v,2))",
        "forall A set:\n    $is_set(frobenius_norm(A,2,3))",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_norm_input")
            .is_err());
    }
}

#[test]
fn matrix_norms_reject_changed_definition_expression() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    for source in [
        include_str!("../../../lean/examples/euclidean_norm_definition/statement.lit"),
        include_str!("../../../lean/examples/frobenius_norm_definition/statement.lit"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let equal = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::NativeMatrix(
                MatrixEqualityProof::ScalarDefinition(proof),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("norm definition")
        };
        proof.expression = Obj::Literal(Literal::Number(Number::new("0".into())));
        assert!(compiler.compile_run(&run, "bad_norm_expression").is_err());
    }
}

#[test]
fn matrix_spaces_and_coordinates_compile_recorded_results() {
    for source in [
        include_str!("../../../lean/examples/matrix_spaces/statement.lit"),
        include_str!("../../../lean/examples/matrix_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_membership/statement.lit"),
        include_str!("../../../lean/examples/matrix_alias/statement.lit"),
        include_str!("../../../lean/examples/zero_matrix/statement.lit"),
        include_str!("../../../lean/examples/zero_matrix_definition/statement.lit"),
        include_str!("../../../lean/examples/zero_matrix_return/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_real/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_twice/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_zero/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_theorem/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose_real/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose_nested/statement.lit"),
        include_str!("../../../lean/examples/matrix_conjugate_transpose_involution/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_involution/statement.lit"),
        include_str!("../../../lean/examples/matrix_addition/statement.lit"),
        include_str!("../../../lean/examples/matrix_subtraction/statement.lit"),
        include_str!("../../../lean/examples/matrix_entrywise_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_addition_commutative/statement.lit"),
        include_str!("../../../lean/examples/matrix_entrywise_real/statement.lit"),
        include_str!("../../../lean/examples/matrix_entrywise_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_scale/statement.lit"),
        include_str!("../../../lean/examples/matrix_scale_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_scale_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_scale_one/statement.lit"),
        include_str!("../../../lean/examples/finite_inner_product/statement.lit"),
        include_str!("../../../lean/examples/finite_inner_product_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_product_real_values/statement.lit"),
        include_str!("../../../lean/examples/matrix_vector_application/statement.lit"),
        include_str!("../../../lean/examples/matrix_vector_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_vector_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_multiplication/statement.lit"),
        include_str!("../../../lean/examples/matrix_multiplication_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_multiplication_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_trace/statement.lit"),
        include_str!("../../../lean/examples/matrix_trace_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_diagonal/statement.lit"),
        include_str!("../../../lean/examples/matrix_diagonal_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_diagonal_formula/statement.lit"),
        include_str!("../../../lean/examples/matrix_diagonal_literal/statement.lit"),
        include_str!("../../../lean/examples/matrix_outer_product/statement.lit"),
        include_str!("../../../lean/examples/matrix_outer_coordinates/statement.lit"),
        include_str!("../../../lean/examples/matrix_outer_definition/statement.lit"),
        include_str!("../../../lean/examples/matrix_outer_transpose/statement.lit"),
        include_str!("../../../lean/examples/finite_sequence_carrier_widening/statement.lit"),
        include_str!("../../../lean/examples/matrix_outer_literal/statement.lit"),
        include_str!("../../../lean/examples/matrix_transpose_twice_real/statement.lit"),
        include_str!("../../../lean/examples/finite_tuple_function_carrier/statement.lit"),
        include_str!("../../../lean/examples/identity_matrix/statement.lit"),
        include_str!("../../../lean/examples/identity_matrix_coordinates/statement.lit"),
        include_str!("../../../lean/examples/identity_matrix_values/statement.lit"),
        include_str!("../../../lean/examples/identity_matrix_formula/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "matrix_spaces").unwrap();
    }
}

#[test]
fn matrix_wd_rejects_missing_or_reordered_natural_dimensions() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("$is_set(matrix(R,2,3))");
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::MatrixSet(wd)),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("matrix WD");
        };
        if missing {
            wd.requirement_fact_verified.pop();
        } else {
            wd.requirement_fact_verified.swap(1, 2);
        }
        assert!(compiler
            .compile_run(&run, "wrong_matrix_dimensions")
            .is_err());
    }
}

#[test]
fn matrix_definition_rejects_changed_signature_domain() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) =
        super::execute("matrix(R,2,3) = fn(row closed_range(1,2),col closed_range(1,3)) R");
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(MatrixEqualityProof::SpaceDefinition(
            proof,
        )),
    ) = &mut equality.searched_proof
    else {
        panic!("matrix definition");
    };
    proof.signature.set_bound_parameters.groups.swap(0, 1);
    assert!(compiler
        .compile_run(&run, "wrong_matrix_signature")
        .is_err());
}

#[test]
fn zero_matrix_rejects_changed_callable_body() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute("zero_matrix(2,3) $in matrix(R,2,3)");
    let atom = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(proof)),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("native matrix function membership")
    };
    proof.callable.function.equal_to =
        Box::new(Obj::Literal(Literal::Number(Number::new("1".into()))));
    assert!(compiler.compile_run(&run, "changed_matrix_body").is_err());
}

#[test]
fn zero_matrix_rejects_changed_component_reduction() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) = super::execute("zero_matrix(2,3)(1,2) = 0");
    let equality = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(
            MatrixEqualityProof::ComponentDefinition(proof),
        ),
    ) = &mut equality.searched_proof
    else {
        panic!("native matrix component definition")
    };
    proof.reduction.value = Obj::Literal(Literal::Number(Number::new("1".into())));
    assert!(compiler
        .compile_run(&run, "changed_matrix_reduction")
        .is_err());
}

#[test]
fn transpose_rejects_missing_input_wd_requirement() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) =
        super::execute("forall A matrix(C,2,3):\n    $is_set(transpose(A,2,3))\n");
    compiler.compile_run(&run, "valid_transpose").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Transpose(
                p,
            )),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("transpose WD")
    };
    p.requirement_fact_verified.pop();
    assert!(compiler
        .compile_run(&run, "missing_transpose_input")
        .is_err());
}

#[test]
fn transpose_rejects_unswapped_body_and_wrong_scalar_premise() {
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof,MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for wrong_premise in [false, true] {
        let (mut run, compiler) =
            super::execute("forall A matrix(R,2,3):\n    transpose(A,2,3) $in matrix(R,3,2)\n");
        compiler.compile_run(&run, "valid_transpose").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("transpose membership")
        };
        if wrong_premise {
            let MatrixFunctionScalarCarrierProof::RealInput(input) = &mut p.callable.scalar_carrier
            else {
                panic!("real input")
            };
            let input = super::atomic_proof_mut(input);
            let AtomicFact::InFact(f) = &mut input.fact else {
                panic!("input membership")
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Obj::FnObj(call) = p.callable.function.equal_to.as_mut() else {
                panic!("transpose body")
            };
            call.body[0].swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "changed_transpose").is_err());
    }
}

#[test]
fn transpose_rejects_changed_component_substitution() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) =
        super::execute("forall A matrix(C,2,3):\n    transpose(A,2,3)(1,2) = A(2,1)\n");
    compiler.compile_run(&run, "valid_transpose").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(
            MatrixEqualityProof::ComponentDefinition(p),
        ),
    ) = &mut equality.searched_proof
    else {
        panic!("transpose component")
    };
    let Obj::FnObj(call) = &mut p.body else {
        panic!("component body")
    };
    call.body[0].swap(0, 1);
    p.reduction.value = p.body.clone();
    assert!(compiler
        .compile_run(&run, "changed_transpose_component")
        .is_err());
}

#[test]
fn nested_matrix_reduction_rejects_changed_body_or_wd_subject() {
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixComponentReductionEvidence, MatrixEqualityProof,
    };
    for wrong_wd in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A matrix(C,2,3):\n    transpose(transpose(A,2,3),3,2)(1,2) = A(1,2)\n",
        );
        compiler
            .compile_run(&run, "valid_nested_transpose")
            .unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::NativeMatrix(
                MatrixEqualityProof::ComponentDefinition(p),
            ),
        ) = &mut equality.searched_proof
        else {
            panic!("nested component")
        };
        let MatrixComponentReductionEvidence::NativeApplication(nested) = &mut p.reduction.evidence
        else {
            panic!("nested reduction")
        };
        if wrong_wd {
            let ObjWellDefinedProof::ByDef { obj, .. } = nested.application_well_defined.as_mut()
            else {
                panic!("nested call WD")
            };
            *obj = Obj::Literal(Literal::Number(Number::new("0".into())));
        } else {
            let Obj::FnObj(call) = &mut nested.body else {
                panic!("expanded body")
            };
            call.body[0].swap(0, 1);
        }
        assert!(compiler
            .compile_run(&run, "changed_nested_transpose")
            .is_err());
    }
}

#[test]
fn conjugate_transpose_rejects_missing_conjugation() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute(
        "forall A matrix(C,2,3):\n    conjugate_transpose(A,2,3) $in matrix(C,3,2)\n",
    );
    compiler
        .compile_run(&run, "valid_conjugate_transpose")
        .unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("conjugate matrix membership")
    };
    let Obj::ComplexOperator(ComplexOperator::Conjugate(c)) = p.callable.function.equal_to.as_ref()
    else {
        panic!("conjugate body")
    };
    p.callable.function.equal_to = c.arg.clone();
    assert!(compiler.compile_run(&run, "missing_conjugate").is_err());
}

#[test]
fn conjugate_transpose_rejects_changed_reduction_endpoint() {
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixComponentReductionEvidence, MatrixEqualityProof,
    };
    let (mut run, compiler) = super::execute(
        "forall A matrix(C,2,3):\n    conjugate_transpose(A,2,3)(1,2) = conj(A(2,1))\n",
    );
    compiler
        .compile_run(&run, "valid_conjugate_component")
        .unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(
            MatrixEqualityProof::ComponentDefinition(p),
        ),
    ) = &mut equality.searched_proof
    else {
        panic!("conjugate component")
    };
    let MatrixComponentReductionEvidence::ConjugateArgument(inner) = &mut p.reduction.evidence
    else {
        panic!("conjugate reduction")
    };
    inner.value = Obj::Literal(Literal::Number(Number::new("0".into())));
    assert!(compiler
        .compile_run(&run, "changed_conjugate_component")
        .is_err());
}

#[test]
fn identity_matrix_rejects_wrong_order_requirement() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) = super::execute("$is_set(identity_matrix(2))");
    compiler.compile_run(&run, "valid_identity_matrix").unwrap();
    let atom = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(
                MatrixOperatorObjWellDefinedProofByDef::IdentityMatrix(p),
            ),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("identity WD")
    };
    let atom = super::atomic_proof_mut(&mut p.requirement_fact_verified[0]);
    let AtomicFact::InFact(f) = &mut atom.fact else {
        panic!("order membership")
    };
    f.set = Obj::StandardSet(StandardSet::R);
    assert!(compiler.compile_run(&run, "wrong_identity_order").is_err());
}

#[test]
fn identity_matrix_rejects_changed_singleton_body() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute("identity_matrix(2) $in matrix(R,2,2)");
    compiler.compile_run(&run, "valid_identity_body").unwrap();
    let atom = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("identity function membership")
    };
    let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) =
        p.callable.function.equal_to.as_mut()
    else {
        panic!("identity body size")
    };
    let Obj::SetOperator(SetOperator::Intersect(intersect)) = size.set.as_mut() else {
        panic!("identity intersection")
    };
    intersect.right = intersect.left.clone();
    assert!(compiler.compile_run(&run, "changed_identity_body").is_err());
}

#[test]
fn identity_matrix_rejects_changed_exact_evaluation() {
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixDefinitionResidualProof, MatrixEqualityProof,
    };
    for changed_body in [false, true] {
        let (mut run, compiler) = super::execute("identity_matrix(3)(1,2) = 0");
        compiler.compile_run(&run, "valid_identity_value").unwrap();
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::NativeMatrix(
                MatrixEqualityProof::ComponentDefinition(p),
            ),
        ) = &mut equality.searched_proof
        else {
            panic!("identity component")
        };
        let MatrixDefinitionResidualProof::ExactEvaluation(value) = p.equality.as_mut() else {
            panic!("exact identity value")
        };
        if changed_body {
            p.body = Obj::Literal(Literal::Number(Number::new("0".into())));
            p.reduction.value = p.body.clone();
        } else {
            value.left_value = Obj::Literal(Literal::Number(Number::new("1".into())));
        }
        assert!(compiler
            .compile_run(&run, "changed_identity_value")
            .is_err());
    }
}

#[test]
fn matrix_entrywise_rejects_wrong_operand_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) =
        super::execute("forall A, B matrix(C,2,3):\n    $is_set(matrix_sub(A,B,2,3))\n");
    compiler.compile_run(&run, "valid_subtraction").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Subtract(
                p,
            )),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("subtraction WD")
    };
    p.requirement_fact_verified.swap(2, 3);
    assert!(compiler
        .compile_run(&run, "wrong_subtraction_operands")
        .is_err());
}

#[test]
fn matrix_entrywise_rejects_changed_operation_or_missing_real_operand() {
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof, MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for missing_operand in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A, B matrix(R,2,3):\n    matrix_add(A,B,2,3) $in matrix(R,2,3)\n",
        );
        compiler.compile_run(&run, "valid_addition").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("addition membership")
        };
        if missing_operand {
            let MatrixFunctionScalarCarrierProof::RealOperands(operands) =
                &mut p.callable.scalar_carrier
            else {
                panic!("real operands")
            };
            operands.pop();
        } else {
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) =
                p.callable.function.equal_to.as_ref()
            else {
                panic!("sum body")
            };
            p.callable.function.equal_to =
                Box::new(Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                    left: sum.left.clone(),
                    right: sum.right.clone(),
                })));
        }
        assert!(compiler
            .compile_run(&run, "wrong_addition_evidence")
            .is_err());
    }
}

#[test]
fn matrix_checked_beta_rejects_changed_expanded_endpoint() {
    use crate::execute::execute_fact_stmt::native_matrix::{
        MatrixDefinitionResidualProof, MatrixEqualityProof, MatrixResidualBeta,
    };
    let (mut run, compiler) = super::execute(
        "forall A, B matrix(C,2,3):\n    matrix_add(A,B,2,3)(1,2) = matrix_add(B,A,2,3)(1,2)\n",
    );
    compiler.compile_run(&run, "valid_matrix_beta").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(
            MatrixEqualityProof::ComponentDefinition(p),
        ),
    ) = &mut equality.searched_proof
    else {
        panic!("matrix component")
    };
    let MatrixDefinitionResidualProof::CheckedBeta(beta) = p.equality.as_mut() else {
        panic!("matrix checked beta")
    };
    let MatrixResidualBeta::Expanded(step) = &mut beta.right else {
        panic!("right expansion")
    };
    step.body = Obj::Literal(Literal::Number(Number::new("0".into())));
    assert!(compiler
        .compile_run(&run, "wrong_matrix_beta_endpoint")
        .is_err());
}

#[test]
fn matrix_scale_rejects_scalar_domain_and_changed_factor() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) =
        super::execute("forall z C, A matrix(C,2,3):\n    $is_set(matrix_scale(z,A,2,3))\n");
    compiler.compile_run(&run, "valid_scale_wd").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Scale(p)),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("scale WD")
    };
    p.requirement_fact_verified.swap(0, 1);
    assert!(compiler.compile_run(&run, "wrong_scale_domain").is_err());

    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute(
        "forall z C, A matrix(C,2,3):\n    matrix_scale(z,A,2,3) $in matrix(C,2,3)\n",
    );
    compiler.compile_run(&run, "valid_scale_body").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("scale membership")
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) =
        p.callable.function.equal_to.as_mut()
    else {
        panic!("scale body")
    };
    mul.left = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
    assert!(compiler.compile_run(&run, "wrong_scale_factor").is_err());
}

#[test]
fn outer_product_rejects_wrong_vector_length_and_coordinate() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for wrong_length in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall a cart_n(C,2), b cart_n(C,3):\n    outer_product(a,b,2,3) $in matrix(C,2,3)\n",
        );
        compiler.compile_run(&run, "valid_outer").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("outer membership")
        };
        if wrong_length {
            let MatrixOperator::OuterProduct(m) = &mut p.callable.operator else {
                panic!("outer operator")
            };
            m.cols = m.rows.clone();
        } else {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) =
                p.callable.function.equal_to.as_mut()
            else {
                panic!("outer body")
            };
            m.right = m.left.clone();
        }
        assert!(compiler
            .compile_run(&run, "wrong_outer_certificate")
            .is_err());
    }
}

#[test]
fn function_set_strategy_rejects_missing_or_changed_requirement() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/finite_sequence_carrier_widening/statement.lit"
        ));
        compiler
            .compile_run(&run, "valid_sequence_widening")
            .unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSetMembership(p),
        ) = &mut atom.searched_proof
        else {
            panic!("function membership strategy")
        };
        if missing {
            p.proof_of_requirement_facts.clear();
        } else {
            let Fact::ForallFact(f) = &mut p.requirement_facts[0] else {
                panic!("pointwise return")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(ret)) =
                &mut f.then_facts[0]
            else {
                panic!("return member")
            };
            ret.set = Obj::StandardSet(StandardSet::Z);
        }
        assert!(compiler.compile_run(&run, "wrong_function_return").is_err());
    }
}

#[test]
fn literal_tuple_function_member_rejects_wrong_coordinates() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,InFactSearchProofByKnownSpecialProperty};
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof, MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for missing in [false, true] {
        let (mut run, compiler) =
            super::execute("outer_product((2,3),(4,5),2,2) $in matrix(R,2,2)");
        compiler.compile_run(&run, "valid_literal_vector").unwrap();
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("outer product membership")
        };
        let MatrixFunctionScalarCarrierProof::RealOperands(operands) =
            &mut p.callable.scalar_carrier
        else {
            panic!("real vectors")
        };
        let MatrixRealOperandProof::Membership(checked) = &mut operands[0] else {
            panic!("vector membership")
        };
        let atom = super::atomic_proof_mut(checked);
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
                InFactSearchProofByKnownSpecialProperty::FiniteTupleInStandardFunctionSpace(p),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("literal tuple function member")
        };
        if missing {
            p.coordinates.pop();
        } else {
            p.coordinates.swap(0, 1);
        }
        assert!(compiler
            .compile_run(&run, "wrong_tuple_coordinates")
            .is_err());
    }
}

#[test]
fn diagonal_matrix_rejects_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("$is_set(diagonal_matrix((2,3),2))");
        compiler.compile_run(&run, "valid_diagonal_wd").unwrap();
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Diagonal(p),
                ),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("diagonal WD")
        };
        if missing {
            p.requirement_fact_verified.pop();
        } else {
            p.requirement_fact_verified.swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "wrong_diagonal_wd").is_err());
    }
}

#[test]
fn diagonal_matrix_rejects_changed_coordinate_body() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let (mut run, compiler) =
        super::execute("forall n N, v cart_n(C,n):\n    diagonal_matrix(v,n) $in matrix(C,n,n)\n");
    compiler.compile_run(&run, "valid_diagonal_body").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("diagonal member")
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) =
        p.callable.function.equal_to.as_mut()
    else {
        panic!("diagonal body")
    };
    mul.left = Box::new(Obj::Literal(Literal::Number(Number::new("1".into()))));
    assert!(compiler.compile_run(&run, "wrong_diagonal_body").is_err());
}

#[test]
fn matrix_trace_rejects_changed_input_domain() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) = super::execute("forall n N,A matrix(C,n,n):\n    trace(A,n) $in C\n");
    compiler.compile_run(&run, "valid_trace").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Trace(p)),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("trace WD")
    };
    p.requirement_fact_verified.swap(0, 1);
    assert!(compiler.compile_run(&run, "wrong_trace_domain").is_err());
}

#[test]
fn matrix_trace_rejects_changed_diagonal_formula() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/matrix_trace_definition/statement.lit"
    ));
    compiler.compile_run(&run, "valid_trace_formula").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let eq = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(MatrixEqualityProof::ScalarDefinition(
            p,
        )),
    ) = &mut eq.searched_proof
    else {
        panic!("trace scalar definition")
    };
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &mut p.expression else {
        panic!("diagonal sum")
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_mut() else {
        panic!("diagonal function")
    };
    f.equal_to = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
    assert!(compiler.compile_run(&run, "wrong_trace_formula").is_err());
}

#[test]
fn matrix_multiply_rejects_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A matrix(C,2,3),B matrix(C,3,4):\n    $is_set(matrix_mul(A,B,2,3,4))\n",
        );
        compiler.compile_run(&run, "valid_product_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Multiply(p),
                ),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("matrix multiply WD")
        };
        if missing {
            p.requirement_fact_verified.pop();
        } else {
            p.requirement_fact_verified.swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "wrong_product_wd").is_err());
    }
}

#[test]
fn matrix_multiply_rejects_changed_summand_or_inner_dimension() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for changed_body in [false, true] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/matrix_multiplication/statement.lit"
        ));
        compiler.compile_run(&run, "valid_product").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("matrix product member")
        };
        let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
            p.callable.function.equal_to.as_mut()
        else {
            panic!("product sum")
        };
        if changed_body {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_mut() else {
                panic!("summand")
            };
            f.equal_to = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        } else {
            let Obj::SetFormer(SetFormer::ClosedRange(range)) = sum.set.as_mut() else {
                panic!("inner index range")
            };
            range.end = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        }
        assert!(compiler.compile_run(&run, "wrong_product_body").is_err());
    }
}

#[test]
fn matrix_apply_rejects_missing_or_reordered_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A matrix(C,2,3),v cart_n(C,3):\n    $is_set(matrix_apply(A,v,2,3))\n",
        );
        compiler.compile_run(&run, "valid_apply_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Apply(
                    p,
                )),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("matrix apply WD")
        };
        if missing {
            p.requirement_fact_verified.pop();
        } else {
            p.requirement_fact_verified.swap(2, 3);
        }
        assert!(compiler.compile_run(&run, "wrong_apply_wd").is_err());
    }
}
#[test]
fn matrix_apply_rejects_changed_summand_or_vector_domain() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixMembershipProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for changed_body in [false, true] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/matrix_vector_application/statement.lit"
        ));
        compiler.compile_run(&run, "valid_apply").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("matrix apply member")
        };
        let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
            p.callable.function.equal_to.as_mut()
        else {
            panic!("apply sum")
        };
        if changed_body {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_mut() else {
                panic!("summand")
            };
            f.equal_to = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        } else {
            let Obj::SetFormer(SetFormer::ClosedRange(range)) = sum.set.as_mut() else {
                panic!("inner index range")
            };
            range.end = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        }
        assert!(compiler.compile_run(&run, "wrong_apply_body").is_err());
    }
}

#[test]
fn inner_product_rejects_changed_vector_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_inner_product/statement.lit"
    ));
    compiler.compile_run(&run, "valid_inner_product").unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(
                MatrixOperatorObjWellDefinedProofByDef::InnerProduct(p),
            ),
        ..
    } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("inner WD")
    };
    p.requirement_fact_verified.swap(1, 2);
    assert!(compiler.compile_run(&run, "wrong_inner_vectors").is_err());
}
#[test]
fn inner_product_rejects_missing_left_conjugation() {
    use crate::execute::execute_fact_stmt::native_matrix::MatrixEqualityProof;
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_inner_product_definition/statement.lit"
    ));
    compiler
        .compile_run(&run, "valid_inner_definition")
        .unwrap();
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let eq = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::NativeMatrix(MatrixEqualityProof::ScalarDefinition(
            p,
        )),
    ) = &mut eq.searched_proof
    else {
        panic!("inner definition")
    };
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &mut p.expression else {
        panic!("inner sum")
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_mut() else {
        panic!("summand")
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = f.equal_to.as_mut() else {
        panic!("product")
    };
    let Obj::ComplexOperator(ComplexOperator::Conjugate(conj)) = mul.left.as_ref() else {
        panic!("conjugate")
    };
    mul.left = conj.arg.clone();
    assert!(compiler
        .compile_run(&run, "wrong_inner_conjugation")
        .is_err());
}
