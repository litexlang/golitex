//! Pure native array layout and real-operand obligations; no proof search.
use super::{matrix_number, real_matrix, real_vector, sub};
use crate::prelude::*;
pub(crate) struct RealFunctionLayout {
    pub rows: Obj,
    pub cols: Obj,
    pub vector: bool,
    pub real_domains: Vec<(Obj, Obj)>,
}
pub(crate) fn extended_layout(operator: &MatrixOperator) -> Option<RealFunctionLayout> {
    let mut real_domains: Vec<(Obj, Obj)> = Vec::new();
    let (rows, cols, vector) = match operator {
        MatrixOperator::Add(x) => {
            real_domains.extend([
                real_matrix(&x.left, &x.rows, &x.cols),
                real_matrix(&x.right, &x.rows, &x.cols),
            ]);
            (x.rows.as_ref().clone(), x.cols.as_ref().clone(), false)
        }
        MatrixOperator::Subtract(x) => {
            real_domains.extend([
                real_matrix(&x.left, &x.rows, &x.cols),
                real_matrix(&x.right, &x.rows, &x.cols),
            ]);
            (x.rows.as_ref().clone(), x.cols.as_ref().clone(), false)
        }
        MatrixOperator::Scale(x) => {
            real_domains.extend([
                real_matrix(&x.matrix, &x.rows, &x.cols),
                (x.scalar.as_ref().clone(), Obj::StandardSet(StandardSet::R)),
            ]);
            (x.rows.as_ref().clone(), x.cols.as_ref().clone(), false)
        }
        MatrixOperator::Multiply(x) => {
            real_domains.extend([
                real_matrix(&x.left, &x.rows, &x.inner),
                real_matrix(&x.right, &x.inner, &x.cols),
            ]);
            (x.rows.as_ref().clone(), x.cols.as_ref().clone(), false)
        }
        MatrixOperator::Apply(x) => {
            real_domains.extend([
                real_matrix(&x.matrix, &x.rows, &x.cols),
                real_vector(&x.vector, &x.cols),
            ]);
            (x.rows.as_ref().clone(), matrix_number(0), true)
        }
        MatrixOperator::Power(x) => {
            real_domains.push(real_matrix(&x.matrix, &x.order, &x.order));
            (x.order.as_ref().clone(), x.order.as_ref().clone(), false)
        }
        MatrixOperator::Inverse(x) => {
            real_domains.push(real_matrix(&x.matrix, &x.order, &x.order));
            (x.order.as_ref().clone(), x.order.as_ref().clone(), false)
        }
        MatrixOperator::Minor(x) => {
            real_domains.push(real_matrix(&x.matrix, &x.order, &x.order));
            let size = sub(x.order.as_ref().clone(), matrix_number(1));
            (size.clone(), size, false)
        }
        MatrixOperator::Adjugate(x) => {
            real_domains.push(real_matrix(&x.matrix, &x.order, &x.order));
            (x.order.as_ref().clone(), x.order.as_ref().clone(), false)
        }
        MatrixOperator::Diagonal(x) => {
            real_domains.push(real_vector(&x.vector, &x.order));
            (x.order.as_ref().clone(), x.order.as_ref().clone(), false)
        }
        MatrixOperator::OuterProduct(x) => {
            real_domains.extend([
                real_vector(&x.left, &x.rows),
                real_vector(&x.right, &x.cols),
            ]);
            (x.rows.as_ref().clone(), x.cols.as_ref().clone(), false)
        }
        MatrixOperator::Determinant(_)
        | MatrixOperator::ZeroMatrix(_)
        | MatrixOperator::IdentityMatrix(_)
        | MatrixOperator::Transpose(_)
        | MatrixOperator::ConjugateTranspose(_)
        | MatrixOperator::Trace(_)
        | MatrixOperator::Rank(_)
        | MatrixOperator::Cofactor(_)
        | MatrixOperator::InnerProduct(_)
        | MatrixOperator::EuclideanNorm(_)
        | MatrixOperator::FrobeniusNorm(_) => return None,
    };
    Some(RealFunctionLayout {
        rows,
        cols,
        vector,
        real_domains,
    })
}
pub(crate) fn real_layout(operator: &MatrixOperator) -> Option<RealFunctionLayout> {
    if let Some(layout) = extended_layout(operator) {
        return Some(layout);
    }
    let (rows, cols, real_domains) = match operator {
        MatrixOperator::ZeroMatrix(x) => (*x.rows.clone(), *x.cols.clone(), vec![]),
        MatrixOperator::IdentityMatrix(x) => (*x.order.clone(), *x.order.clone(), vec![]),
        MatrixOperator::Transpose(x) => (
            *x.cols.clone(),
            *x.rows.clone(),
            vec![real_matrix(&x.matrix, &x.rows, &x.cols)],
        ),
        MatrixOperator::ConjugateTranspose(x) => (
            *x.cols.clone(),
            *x.rows.clone(),
            vec![real_matrix(&x.matrix, &x.rows, &x.cols)],
        ),
        _ => return None,
    };
    Some(RealFunctionLayout {
        rows,
        cols,
        vector: false,
        real_domains,
    })
}
