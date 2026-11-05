use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;

const SOURCE: &str = r#"# Every finite complex matrix has a rank-sized factorization with split left and right inverses.
thm checked_rank_factorization_exists_conjoined:
    ? forall m, n N, A matrix(C,m,n):
        exist U matrix(C,m,matrix_rank(A,m,n)), V matrix(C,matrix_rank(A,m,n),n), L matrix(C,matrix_rank(A,m,n),m), Rr matrix(C,n,matrix_rank(A,m,n)) st {A=matrix_mul(U,V,m,matrix_rank(A,m,n),n) and matrix_mul(L,U,matrix_rank(A,m,n),m,matrix_rank(A,m,n))=identity_matrix(matrix_rank(A,m,n)) and matrix_mul(V,Rr,matrix_rank(A,m,n),n,matrix_rank(A,m,n))=identity_matrix(matrix_rank(A,m,n))}
    release thm matrix_rank_factorization_exists(A,m,n)
"#;
const WITNESSES: &str = r#"# Choose split factorization witnesses and use their two factors to prove the usual rank factorization.
thm checked_rank_factorization_witness_consumption:
    ? forall m, n N, A matrix(C,m,n):
        exist B matrix(C,m,matrix_rank(A,m,n)), D matrix(C,matrix_rank(A,m,n),n) st {A=matrix_mul(B,D,m,matrix_rank(A,m,n),n)}
    release thm matrix_rank_factorization_exists(A,m,n)
    have U matrix(C,m,matrix_rank(A,m,n)), V matrix(C,matrix_rank(A,m,n),n), L matrix(C,matrix_rank(A,m,n),m), Rr matrix(C,n,matrix_rank(A,m,n)):
        A=matrix_mul(U,V,m,matrix_rank(A,m,n),n) and matrix_mul(L,U,matrix_rank(A,m,n),m,matrix_rank(A,m,n))=identity_matrix(matrix_rank(A,m,n)) and matrix_mul(V,Rr,matrix_rank(A,m,n),n,matrix_rank(A,m,n))=identity_matrix(matrix_rank(A,m,n))
    witness exist B matrix(C,m,matrix_rank(A,m,n)), D matrix(C,matrix_rank(A,m,n),n) st {A=matrix_mul(B,D,m,matrix_rank(A,m,n),n)} from U,V
"#;
fn exists(b: &mut BuiltinThmApplication) -> &mut PlainExistFact {
    let Fact::ExistFact(f) = &mut b.conclusions[0] else {
        panic!()
    };
    f
}
fn conjunction(b: &mut BuiltinThmApplication) -> &mut AndFact {
    let [QuantifierFreeFact::AndFact(f)] = exists(b).facts.as_mut_slice() else {
        panic!()
    };
    f
}

#[test]
fn rank_existence_retains_three_ordered_context_proofs_stores_and_output_wd() {
    for change in [
        "proof",
        "store",
        "context",
        "conclusion",
        "wd",
        "order",
        "stores",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        assert_eq!(call.dom_proofs.len(), 3);
        match change {
            "proof" => {
                call.dom_proofs.pop();
            }
            "store" => {
                call.dom_stores.pop();
            }
            "context" => {
                call.builtin.as_mut().unwrap().requirements.pop();
            }
            "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
            "wd" => call.conclusions_wd.clear(),
            "order" => call.dom_proofs.swap(0, 1),
            _ => call.dom_stores.swap(0, 1),
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_retains_both_naturals_and_exact_rectangular_complex_context() {
    for change in [
        "rows_natural",
        "cols_natural",
        "carrier",
        "rows",
        "cols",
        "subject",
        "fact_id",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let index = match change {
            "rows_natural" => 0,
            "cols_natural" => 1,
            _ => 2,
        };
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
            panic!()
        };
        match change {
            "rows_natural" | "cols_natural" => f.set = Obj::StandardSet(StandardSet::Z),
            "subject" => f.element = super::number_object("0"),
            "fact_id" => f.fact_id = FactId::new(u64::MAX),
            _ => {
                let Obj::SetFormer(SetFormer::MatrixSet(s)) = &mut f.set else {
                    panic!()
                };
                match change {
                    "carrier" => s.set = Box::new(Obj::StandardSet(StandardSet::R)),
                    "rows" => s.rows = Box::new(super::number_object("99")),
                    _ => s.cols = Box::new(super::number_object("99")),
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_requires_four_distinct_original_matrix_witness_domains() {
    for change in [
        "groups", "count", "identity", "carrier", "u_rows", "v_cols", "l_rows", "r_cols",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let f = exists(invocation(&mut run).builtin.as_mut().unwrap());
        match change {
            "groups" => {
                f.typed_parameters.groups.pop();
            }
            "count" => f.typed_parameters.groups[0].params.clear(),
            "identity" => {
                f.typed_parameters.groups[1].params[0].id =
                    f.typed_parameters.groups[0].params[0].id
            }
            _ => {
                let index = match change {
                    "v_cols" => 1,
                    "l_rows" => 2,
                    "r_cols" => 3,
                    _ => 0,
                };
                let ParamType::Obj(Obj::SetFormer(SetFormer::MatrixSet(s))) =
                    &mut f.typed_parameters.groups[index].param_type
                else {
                    panic!()
                };
                if change == "carrier" {
                    s.set = Box::new(Obj::StandardSet(StandardSet::R));
                } else if change.ends_with("rows") {
                    s.rows = Box::new(super::number_object("99"));
                } else {
                    s.cols = Box::new(super::number_object("99"));
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_preserves_original_rank_subject_and_two_dimensions() {
    for change in ["subject", "rows", "cols", "rank_kind"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let f = exists(invocation(&mut run).builtin.as_mut().unwrap());
        let ParamType::Obj(Obj::SetFormer(SetFormer::MatrixSet(s))) =
            &mut f.typed_parameters.groups[0].param_type
        else {
            panic!()
        };
        if change == "rank_kind" {
            s.cols = Box::new(super::number_object("1"));
        } else {
            let Obj::MatrixOperator(MatrixOperator::Rank(r)) = s.cols.as_mut() else {
                panic!()
            };
            match change {
                "subject" => r.matrix = Box::new(super::number_object("0")),
                "rows" => r.rows = Box::new(super::number_object("99")),
                _ => r.cols = Box::new(super::number_object("99")),
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_preserves_one_three_equality_conjunction_and_split_orientations() {
    for change in [
        "body",
        "count",
        "order",
        "factor_side",
        "factor_operands",
        "left_split",
        "right_split",
        "identity_size",
        "inner_size",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "body" {
            exists(b).facts.clear();
        } else {
            let f = conjunction(b);
            if change == "count" {
                f.facts.pop();
            } else if change == "order" {
                f.facts.swap(1, 2);
            } else {
                let i = match change {
                    "left_split" | "identity_size" => 1,
                    "right_split" => 2,
                    _ => 0,
                };
                let AtomicFact::EqualFact(e) = &mut f.facts[i] else {
                    panic!()
                };
                if change == "factor_side" {
                    std::mem::swap(&mut e.left, &mut e.right);
                } else if change == "identity_size" {
                    let Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) = &mut e.right
                    else {
                        panic!()
                    };
                    p.order = Box::new(super::number_object("99"));
                } else {
                    let obj = if i == 0 { &mut e.right } else { &mut e.left };
                    let Obj::MatrixOperator(MatrixOperator::Multiply(p)) = obj else {
                        panic!()
                    };
                    if change == "inner_size" {
                        p.inner = Box::new(super::number_object("99"));
                    } else {
                        std::mem::swap(&mut p.left, &mut p.right);
                    }
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_retains_original_existential_wd_binders_stores_and_body() {
    for change in ["types", "stores", "bodies", "store_order", "rank_subject"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        let FactWellDefinedProof::ExistFact(wd) = &mut call.conclusions_wd[0] else {
            panic!()
        };
        let d = wd.as_detailed_mut().unwrap();
        match change {
            "types" => {
                d.introduced_params.param_type_well_defined.pop();
            }
            "stores" => {
                d.introduced_params
                    .defined_params
                    .store_and_infer_results
                    .pop();
            }
            "bodies" => d.assumed_body_facts.clear(),
            "store_order" => d
                .introduced_params
                .defined_params
                .store_and_infer_results
                .swap(0, 1),
            _ => {
                let ParamTypeWellDefinedProof::Obj(matrix) =
                    &mut d.introduced_params.param_type_well_defined[0]
                else {
                    panic!()
                };
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::SetFormer(
                            SetFormerObjWellDefinedProofByDef::MatrixSet(p),
                        ),
                    ..
                } = matrix.as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                let DetailedObjWellDefinedProof::ByDef { obj, .. } =
                    p.child_obj_well_defined[2].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                *obj = super::number_object("0");
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_existence_rejects_future_existential_as_original_matrix_evidence() {
    let (mut run, compiler) = super::execute(SOURCE);
    let call = invocation(&mut run);
    let id = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let child = super::atomic_proof_mut(&mut call.dom_proofs[2]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut child.searched_proof
    else {
        panic!("original matrix assumption")
    };
    cite.cite_fact_id = id;
    assert!(compiler.compile_run(&run, "future_rank_exists").is_err());
}

#[test]
fn rank_existence_rejects_changed_native_rule_derivation_and_call_arguments() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for change in ["rule", "derivation", "arguments", "unique", "negative"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "rule" => {
                call.builtin.as_mut().unwrap().theorem =
                    crate::builtin_theorem::BuiltinTheoremId::MatrixRankBounds
            }
            "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
            "arguments" => call.builtin.as_mut().unwrap().arguments.swap(1, 2),
            _ => {
                let b = call.builtin.as_mut().unwrap();
                let f = exists(b).clone();
                b.conclusions[0] = if change == "unique" {
                    Fact::ExistUniqueFact(f)
                } else {
                    Fact::NotExistFact(f)
                };
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_exists_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn rank_witness_elimination_rejects_missing_carrier_wd_and_future_citations() {
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
    use crate::execute::ExecHaveObjByExistFactsStmtResult;
    for change in ["carrier", "store_order", "future"] {
        let (mut run, compiler) = super::execute(WITNESSES);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(p),
            ),
        )) = &mut body.proof_steps[1]
        else {
            panic!("original four-witness choice")
        };
        match change {
            "carrier" => {
                p.verify_exist
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .param_type_well_defined
                    .pop();
            }
            "store_order" => p.store_and_infer_result.store_and_infer_results.swap(0, 1),
            _ => {
                let future = p
                    .store_and_infer_result
                    .store_and_infer_results
                    .last()
                    .unwrap()
                    .primary_fact_id();
                let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) =
                    &mut p.verify_exist.searched_proof
                else {
                    panic!("original preceding existential")
                };
                cite.cite_fact_id = future;
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_rank_witness_{change}"))
                .is_err(),
            "{change}"
        );
    }
}
