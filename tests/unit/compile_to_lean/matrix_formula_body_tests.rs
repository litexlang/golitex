use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionSpaceObjWellDefinedProofByDef, MatrixOperatorObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;

const SOURCE: &str = r#"# Elementary matrix operations remain available inside formula functions.
have fn transpose_real(A matrix(R,2,3)) matrix(R,3,2) = transpose(A,2,3)
have fn adjoint_complex(A matrix(C,2,3)) matrix(C,3,2) = conjugate_transpose(A,2,3)
have fn matrix_sum(A,B matrix(R,2,3)) matrix(R,2,3) = matrix_add(A,B,2,3)
have fn matrix_difference(A,B matrix(C,2,3)) matrix(C,2,3) = matrix_sub(A,B,2,3)
have fn scaled_matrix(k R,A matrix(R,2,3)) matrix(R,2,3) = matrix_scale(k,A,2,3)
forall A matrix(R,2,3):
    transpose_real(A) = transpose(A,2,3)
forall A matrix(C,2,3):
    adjoint_complex(A) = conjugate_transpose(A,2,3)
forall A,B matrix(R,2,3):
    matrix_sum(A,B) = matrix_add(A,B,2,3)
forall A,B matrix(C,2,3):
    matrix_difference(A,B) = matrix_sub(A,B,2,3)
forall k R,A matrix(R,2,3):
    scaled_matrix(k,A) = matrix_scale(k,A,2,3)
have beta_rows,beta_cols N
have fn transpose_sized(A matrix(R,beta_rows,beta_cols)) matrix(R,beta_cols,beta_rows) = transpose(A,beta_rows,beta_cols)
forall A matrix(R,beta_rows,beta_cols):
    transpose_sized(A) = transpose(A,beta_rows,beta_cols)
have fn transpose_empty(A matrix(R,0,3)) matrix(R,3,0) = transpose(A,0,3)
"#;
const ZERO_SOURCE: &str = r#"# Zero-matrix formula functions preserve their captured dimensions, including zero rows.
have fn zero_shape(t R) matrix(R,2,3) = zero_matrix(2,3)
forall t R:
    zero_shape(t) = zero_matrix(2,3)
have zero_rows,zero_cols N
have fn zero_captured(t R) matrix(R,zero_rows,zero_cols) = zero_matrix(zero_rows,zero_cols)
forall t R:
    zero_captured(t) = zero_matrix(zero_rows,zero_cols)
have fn zero_empty(t R) matrix(R,0,3) = zero_matrix(0,3)
forall t R:
    zero_empty(t) = zero_matrix(0,3)
zero_shape(0)(1,2) = 0
"#;
const SCALAR_SOURCES: &[(&str, &str)] = &[
    (
        r#"# Matrix traces define scalar-valued functions, including captured and empty dimensions.
have fn trace_formula(A matrix(C,2,2)) C = trace(A,2)
forall A matrix(C,2,2):
    trace_formula(A) = trace(A,2)
have trace_order N
have fn real_trace_formula(A matrix(R,trace_order,trace_order)) R = trace(A,trace_order)
forall A matrix(R,trace_order,trace_order):
    real_trace_formula(A) = trace(A,trace_order)
have fn empty_trace_formula(A matrix(C,0,0)) C = trace(A,0)
forall A matrix(C,0,0):
    empty_trace_formula(A) = trace(A,0)
have fn shifted_trace_formula(A matrix(C,2,2)) C = trace(A,2) + 1
forall A matrix(C,2,2):
    shifted_trace_formula(A) = trace(A,2) + 1
"#,
        "matrixTraceRawValue",
    ),
    (
        r#"# Finite complex inner products define functions with conjugation on the left operand.
have fn inner_formula(v,w cart_n(C,2)) C = inner_product(v,w,2)
forall v,w cart_n(C,2):
    inner_formula(v,w) = inner_product(v,w,2)
have inner_dimension N
have fn real_inner_formula(v,w cart_n(R,inner_dimension)) R = inner_product(v,w,inner_dimension)
forall v,w cart_n(R,inner_dimension):
    real_inner_formula(v,w) = inner_product(v,w,inner_dimension)
have fn empty_inner_formula(v,w cart_n(C,0)) C = inner_product(v,w,0)
forall v,w cart_n(C,0):
    empty_inner_formula(v,w) = inner_product(v,w,0)
have fn shifted_inner_formula(v,w cart_n(C,2)) C = inner_product(v,w,2) + 1
forall v,w cart_n(C,2):
    shifted_inner_formula(v,w) = inner_product(v,w,2) + 1
"#,
        "finiteInnerProductRawValue",
    ),
    (
        r#"# Frobenius norms define real-valued functions on complex matrices, including empty matrices.
have fn frobenius_formula(A matrix(C,2,3)) R = frobenius_norm(A,2,3)
forall A matrix(C,2,3):
    frobenius_formula(A) = frobenius_norm(A,2,3)
have norm_rows,norm_cols N
have fn captured_frobenius_formula(A matrix(R,norm_rows,norm_cols)) R = frobenius_norm(A,norm_rows,norm_cols)
forall A matrix(R,norm_rows,norm_cols):
    captured_frobenius_formula(A) = frobenius_norm(A,norm_rows,norm_cols)
have fn empty_frobenius_formula(A matrix(C,0,3)) R = frobenius_norm(A,0,3)
forall A matrix(C,0,3):
    empty_frobenius_formula(A) = frobenius_norm(A,0,3)
have fn shifted_frobenius_formula(A matrix(C,2,3)) R = frobenius_norm(A,2,3) + 1
forall A matrix(C,2,3):
    shifted_frobenius_formula(A) = frobenius_norm(A,2,3) + 1
"#,
        "frobeniusNormRawSum",
    ),
];

const GRAPH_SOURCES: &[(&str, &str)] = &[
    (
        r#"# Rectangular matrix product functions retain compatible dimensions, real/complex carriers and empty inner sums.
have fn rectangular_product(A matrix(C,2,3),B matrix(C,3,4)) matrix(C,2,4) = matrix_mul(A,B,2,3,4)

forall A matrix(C,2,3),B matrix(C,3,4):
    rectangular_product(A,B) = matrix_mul(A,B,2,3,4)

have product_rows,product_inner,product_cols N

have fn real_product(A matrix(R,product_rows,product_inner),B matrix(R,product_inner,product_cols)) matrix(R,product_rows,product_cols) = matrix_mul(A,B,product_rows,product_inner,product_cols)

forall A matrix(R,product_rows,product_inner),B matrix(R,product_inner,product_cols):
    real_product(A,B) = matrix_mul(A,B,product_rows,product_inner,product_cols)

have fn empty_product(A matrix(C,2,0),B matrix(C,0,3)) matrix(C,2,3) = matrix_mul(A,B,2,0,3)

forall A matrix(C,2,0),B matrix(C,0,3):
    empty_product(A,B) = matrix_mul(A,B,2,0,3)

have fn product_transpose(A matrix(C,2,3),B matrix(C,3,4)) matrix(C,4,2) = transpose(matrix_mul(A,B,2,3,4),2,4)

forall A matrix(C,2,3),B matrix(C,3,4):
    product_transpose(A,B) = transpose(matrix_mul(A,B,2,3,4),2,4)

forall A matrix(C,2,3),B matrix(C,3,4):
    rectangular_product(A,B)(1,2) $in C
"#,
        "matrixMultiplyRawBody",
    ),
    (
        r#"# Finite-vector functions construct diagonal matrices, including captured or zero order and addition of the identity.
have fn diagonal_formula(v cart_n(C,2)) matrix(C,2,2) = diagonal_matrix(v,2)

forall v cart_n(C,2):
    diagonal_formula(v) = diagonal_matrix(v,2)

have diagonal_order N

have fn real_diagonal_formula(v cart_n(R,diagonal_order)) matrix(R,diagonal_order,diagonal_order) = diagonal_matrix(v,diagonal_order)

forall v cart_n(R,diagonal_order):
    real_diagonal_formula(v) = diagonal_matrix(v,diagonal_order)

have fn empty_diagonal_formula(v cart_n(C,0)) matrix(C,0,0) = diagonal_matrix(v,0)

forall v cart_n(C,0):
    empty_diagonal_formula(v) = diagonal_matrix(v,0)

have fn shifted_diagonal_formula(v cart_n(C,2)) matrix(C,2,2) = matrix_add(diagonal_matrix(v,2),identity_matrix(2),2,2)

forall v cart_n(C,2):
    shifted_diagonal_formula(v) = matrix_add(diagonal_matrix(v,2),identity_matrix(2),2,2)

forall v cart_n(C,2):
    diagonal_formula(v)(1,2) $in C
"#,
        "matrixDiagonalBody",
    ),
    (
        r#"# Two-vector functions construct outer products, including captured dimensions, empty rows and transpose.
have fn outer_formula(v cart_n(C,2),w cart_n(C,3)) matrix(C,2,3) = outer_product(v,w,2,3)

forall v cart_n(C,2),w cart_n(C,3):
    outer_formula(v,w) = outer_product(v,w,2,3)

have outer_rows,outer_cols N

have fn real_outer_formula(v cart_n(R,outer_rows),w cart_n(R,outer_cols)) matrix(R,outer_rows,outer_cols) = outer_product(v,w,outer_rows,outer_cols)

forall v cart_n(R,outer_rows),w cart_n(R,outer_cols):
    real_outer_formula(v,w) = outer_product(v,w,outer_rows,outer_cols)

have fn empty_outer_formula(v cart_n(C,0),w cart_n(C,3)) matrix(C,0,3) = outer_product(v,w,0,3)

forall v cart_n(C,0),w cart_n(C,3):
    empty_outer_formula(v,w) = outer_product(v,w,0,3)

have fn outer_transpose(v cart_n(C,2),w cart_n(C,3)) matrix(C,3,2) = transpose(outer_product(v,w,2,3),2,3)

forall v cart_n(C,2),w cart_n(C,3):
    outer_transpose(v,w) = transpose(outer_product(v,w,2,3),2,3)

forall v cart_n(C,2),w cart_n(C,3):
    outer_formula(v,w)(1,2) $in C
"#,
        "matrixOuterBody",
    ),
    (
        r#"# Matrix-power functions retain natural exponents, captured dimensions, zero order and returned coordinates.
have fn power_formula(A matrix(C,2,2),k N) matrix(C,2,2) = matrix_power(A,2,k)

forall A matrix(C,2,2),k N:
    power_formula(A,k) = matrix_power(A,2,k)

have power_order,power_exponent N

have fn real_power_formula(A matrix(R,power_order,power_order)) matrix(R,power_order,power_order) = matrix_power(A,power_order,power_exponent)

forall A matrix(R,power_order,power_order):
    real_power_formula(A) = matrix_power(A,power_order,power_exponent)

have fn empty_power_formula(A matrix(C,0,0)) matrix(C,0,0) = matrix_power(A,0,3)

forall A matrix(C,0,0):
    empty_power_formula(A) = matrix_power(A,0,3)

have fn transposed_square(A matrix(C,2,2)) matrix(C,2,2) = transpose(matrix_power(A,2,2),2,2)

forall A matrix(C,2,2):
    transposed_square(A) = transpose(matrix_power(A,2,2),2,2)

forall A matrix(C,2,2),k N:
    power_formula(A,k)(1,2) $in C
"#,
        "matrixPowerRawValue",
    ),
    (
        r#"# Deleted-row/column functions retain positive order, legal indices and the original n-1 output dimensions.
have fn minor_formula(A matrix(C,3,3),r,c closed_range(1,3)) matrix(C,3-1,3-1) = matrix_minor(A,3,r,c)

forall A matrix(C,3,3),r,c closed_range(1,3):
    minor_formula(A,r,c) = matrix_minor(A,3,r,c)

have minor_order N+

have fn real_minor_formula(A matrix(R,minor_order,minor_order),r,c closed_range(1,minor_order)) matrix(R,minor_order-1,minor_order-1) = matrix_minor(A,minor_order,r,c)

forall A matrix(R,minor_order,minor_order),r,c closed_range(1,minor_order):
    real_minor_formula(A,r,c) = matrix_minor(A,minor_order,r,c)

have fn empty_minor_formula(A matrix(C,1,1)) matrix(C,1-1,1-1) = matrix_minor(A,1,1,1)

forall A matrix(C,1,1):
    empty_minor_formula(A) = matrix_minor(A,1,1,1)

have fn transposed_minor(A matrix(C,3,3)) matrix(C,3-1,3-1) = transpose(matrix_minor(A,3,1,2),3-1,3-1)

forall A matrix(C,3,3):
    transposed_minor(A) = transpose(matrix_minor(A,3,1,2),3-1,3-1)

forall A matrix(C,3,3),r,c closed_range(1,3):
    minor_formula(A,r,c)(1,2) $in C
"#,
        "matrixMinorBody",
    ),
    (
        r#"# Adjugate functions retain real/complex matrices, captured or empty dimensions and returned coordinates.
have fn adjugate_formula(A matrix(C,2,2)) matrix(C,2,2) = matrix_adjugate(A,2)

forall A matrix(C,2,2):
    adjugate_formula(A) = matrix_adjugate(A,2)

have adjugate_order N

have fn real_adjugate_formula(A matrix(R,adjugate_order,adjugate_order)) matrix(R,adjugate_order,adjugate_order) = matrix_adjugate(A,adjugate_order)

forall A matrix(R,adjugate_order,adjugate_order):
    real_adjugate_formula(A) = matrix_adjugate(A,adjugate_order)

have fn empty_adjugate_formula(A matrix(C,0,0)) matrix(C,0,0) = matrix_adjugate(A,0)

forall A matrix(C,0,0):
    empty_adjugate_formula(A) = matrix_adjugate(A,0)

have fn transposed_adjugate(A matrix(C,2,2)) matrix(C,2,2) = transpose(matrix_adjugate(A,2),2,2)

forall A matrix(C,2,2):
    transposed_adjugate(A) = transpose(matrix_adjugate(A,2),2,2)

forall A matrix(C,2,2):
    adjugate_formula(A)(1,2) $in C
"#,
        "matrixCofactorRawValue",
    ),
    (
        r#"# Inverse functions consume nonzero determinant proofs; the zero-order case proves its determinant is one.
have fn inverse_formula(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = matrix_inv(A,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A) = matrix_inv(A,2)

have inverse_order N

have fn real_inverse_formula(A matrix(R,inverse_order,inverse_order): det(A,inverse_order) != 0) matrix(R,inverse_order,inverse_order) = matrix_inv(A,inverse_order)

forall A matrix(R,inverse_order,inverse_order):
    det(A,inverse_order) != 0
    =>:
        real_inverse_formula(A) = matrix_inv(A,inverse_order)

forall A matrix(C,0,0):
    det(A,0) = 1

claim:
    ? forall A matrix(C,0,0):
        det(A,0) != 0
    det(A,0) = 1
    det(A,0) != 0

have fn empty_inverse_formula(A matrix(C,0,0)) matrix(C,0,0) = matrix_inv(A,0)

forall A matrix(C,0,0):
    empty_inverse_formula(A) = matrix_inv(A,0)

have fn transposed_inverse(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        transposed_inverse(A) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A)(1,2) $in C
"#,
        "M.divValue",
    ),
];

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
    let source = r#"# Inverse functions consume nonzero determinant proofs; the zero-order case proves its determinant is one.
have fn inverse_formula(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = matrix_inv(A,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A) = matrix_inv(A,2)

have inverse_order N

have fn real_inverse_formula(A matrix(R,inverse_order,inverse_order): det(A,inverse_order) != 0) matrix(R,inverse_order,inverse_order) = matrix_inv(A,inverse_order)

forall A matrix(R,inverse_order,inverse_order):
    det(A,inverse_order) != 0
    =>:
        real_inverse_formula(A) = matrix_inv(A,inverse_order)

forall A matrix(C,0,0):
    det(A,0) = 1

claim:
    ? forall A matrix(C,0,0):
        det(A,0) != 0
    det(A,0) = 1
    det(A,0) != 0

have fn empty_inverse_formula(A matrix(C,0,0)) matrix(C,0,0) = matrix_inv(A,0)

forall A matrix(C,0,0):
    empty_inverse_formula(A) = matrix_inv(A,0)

have fn transposed_inverse(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        transposed_inverse(A) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A)(1,2) $in C
"#;
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
    let source = r#"# Inverse functions consume nonzero determinant proofs; the zero-order case proves its determinant is one.
have fn inverse_formula(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = matrix_inv(A,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A) = matrix_inv(A,2)

have inverse_order N

have fn real_inverse_formula(A matrix(R,inverse_order,inverse_order): det(A,inverse_order) != 0) matrix(R,inverse_order,inverse_order) = matrix_inv(A,inverse_order)

forall A matrix(R,inverse_order,inverse_order):
    det(A,inverse_order) != 0
    =>:
        real_inverse_formula(A) = matrix_inv(A,inverse_order)

forall A matrix(C,0,0):
    det(A,0) = 1

claim:
    ? forall A matrix(C,0,0):
        det(A,0) != 0
    det(A,0) = 1
    det(A,0) != 0

have fn empty_inverse_formula(A matrix(C,0,0)) matrix(C,0,0) = matrix_inv(A,0)

forall A matrix(C,0,0):
    empty_inverse_formula(A) = matrix_inv(A,0)

have fn transposed_inverse(A matrix(C,2,2): det(A,2) != 0) matrix(C,2,2) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        transposed_inverse(A) = transpose(matrix_inv(A,2),2,2)

forall A matrix(C,2,2):
    det(A,2) != 0
    =>:
        inverse_formula(A)(1,2) $in C
"#;
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
