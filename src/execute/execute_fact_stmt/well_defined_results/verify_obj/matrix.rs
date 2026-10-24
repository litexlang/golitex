//! Formation checks for matrix spaces and native operations. Dimensions are
//! natural-number requirements, independent of integer interval formation.
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::prelude::*;

impl Runtime {
    pub(super) fn verify_matrix_set_well_definedness_by_def(
        &mut self,
        value: &MatrixSet,
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let children =
            self.verify_objs_as_children(&[&value.set, &value.rows, &value.cols], state)?;
        let requirements = vec![
            self.require_is_set(
                &value.set,
                state,
                "matrix element carrier must be a set".into(),
            )?,
            self.require_obj_in_standard_set(
                &value.rows,
                StandardSet::N,
                state,
                "matrix rows must be natural".into(),
            )?,
            self.require_obj_in_standard_set(
                &value.cols,
                StandardSet::N,
                state,
                "matrix columns must be natural".into(),
            )?,
        ];
        Ok(self.with_requirements(children, requirements))
    }

    pub(super) fn verify_matrix_operator_well_definedness_by_def(
        &mut self,
        value: &MatrixOperator,
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        match value {
            MatrixOperator::Determinant(x) => {
                self.verify_matrix_square_operation(&x.matrix, &x.order, state)
            }
            MatrixOperator::Trace(x) => {
                self.verify_matrix_square_operation(&x.matrix, &x.order, state)
            }
            MatrixOperator::ZeroMatrix(x) => {
                self.verify_matrix_dimensions(&[x.rows.as_ref(), &x.cols], state)
            }
            MatrixOperator::IdentityMatrix(x) => self.verify_matrix_dimensions(&[&x.order], state),
            MatrixOperator::Transpose(x) => self.verify_matrix_rectangular_operation(
                &x.matrix,
                x.rows.as_ref(),
                x.cols.as_ref(),
                state,
            ),
            MatrixOperator::ConjugateTranspose(x) => self.verify_matrix_rectangular_operation(
                &x.matrix,
                x.rows.as_ref(),
                x.cols.as_ref(),
                state,
            ),
            MatrixOperator::Add(_)
            | MatrixOperator::Subtract(_)
            | MatrixOperator::Scale(_)
            | MatrixOperator::Multiply(_)
            | MatrixOperator::Apply(_)
            | MatrixOperator::Power(_)
            | MatrixOperator::Inverse(_)
            | MatrixOperator::Rank(_)
            | MatrixOperator::Minor(_)
            | MatrixOperator::Cofactor(_)
            | MatrixOperator::Adjugate(_)
            | MatrixOperator::Diagonal(_)
            | MatrixOperator::OuterProduct(_)
            | MatrixOperator::InnerProduct(_)
            | MatrixOperator::EuclideanNorm(_)
            | MatrixOperator::FrobeniusNorm(_) => {
                self.verify_extended_matrix_operation(value, state)
            }
        }
    }

    fn verify_extended_matrix_operation(
        &mut self,
        value: &MatrixOperator,
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        use crate::execute::execute_fact_stmt::native_matrix::{matrix_number, matrix_space};
        let children = self.verify_objs_as_children(&value.operand_refs(), state)?;
        let mut domains: Vec<(Obj, Obj)> = Vec::new();
        let mut matrices: Vec<(&Obj, &Obj, &Obj)> = Vec::new();
        let mut vectors: Vec<(&Obj, &Obj)> = Vec::new();
        let mut dimensions: Vec<&Obj> = Vec::new();
        match value {
            MatrixOperator::Add(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.extend([
                    (x.left.as_ref(), x.rows.as_ref(), x.cols.as_ref()),
                    (x.right.as_ref(), x.rows.as_ref(), x.cols.as_ref()),
                ]);
            }
            MatrixOperator::Subtract(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.extend([
                    (x.left.as_ref(), x.rows.as_ref(), x.cols.as_ref()),
                    (x.right.as_ref(), x.rows.as_ref(), x.cols.as_ref()),
                ]);
            }
            MatrixOperator::Scale(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.push((&x.matrix, x.rows.as_ref(), x.cols.as_ref()));
                domains.push((x.scalar.as_ref().clone(), Obj::StandardSet(StandardSet::C)));
            }
            MatrixOperator::Multiply(x) => {
                dimensions.extend([x.rows.as_ref(), x.inner.as_ref(), x.cols.as_ref()]);
                matrices.extend([
                    (x.left.as_ref(), x.rows.as_ref(), x.inner.as_ref()),
                    (x.right.as_ref(), x.inner.as_ref(), x.cols.as_ref()),
                ]);
            }
            MatrixOperator::Apply(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.push((&x.matrix, x.rows.as_ref(), x.cols.as_ref()));
                vectors.push((&x.vector, x.cols.as_ref()));
            }
            MatrixOperator::Power(x) => {
                dimensions.extend([x.order.as_ref(), x.exponent.as_ref()]);
                matrices.push((&x.matrix, &x.order, &x.order));
            }
            MatrixOperator::Inverse(x) => {
                dimensions.push(&x.order);
                matrices.push((&x.matrix, &x.order, &x.order));
            }
            MatrixOperator::Rank(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.push((&x.matrix, x.rows.as_ref(), x.cols.as_ref()));
            }
            MatrixOperator::Minor(x) => {
                dimensions.push(&x.order);
                matrices.push((&x.matrix, &x.order, &x.order));
                domains.extend([
                    (
                        x.order.as_ref().clone(),
                        Obj::StandardSet(StandardSet::NPos),
                    ),
                    (x.row.as_ref().clone(), matrix_index_set(&x.order)),
                    (x.col.as_ref().clone(), matrix_index_set(&x.order)),
                ]);
            }
            MatrixOperator::Cofactor(x) => {
                dimensions.push(&x.order);
                matrices.push((&x.matrix, &x.order, &x.order));
                domains.extend([
                    (
                        x.order.as_ref().clone(),
                        Obj::StandardSet(StandardSet::NPos),
                    ),
                    (x.row.as_ref().clone(), matrix_index_set(&x.order)),
                    (x.col.as_ref().clone(), matrix_index_set(&x.order)),
                ]);
            }
            MatrixOperator::Adjugate(x) => {
                dimensions.push(&x.order);
                matrices.push((&x.matrix, &x.order, &x.order));
            }
            MatrixOperator::Diagonal(x) => {
                dimensions.push(&x.order);
                vectors.push((&x.vector, &x.order));
            }
            MatrixOperator::OuterProduct(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                vectors.extend([
                    (x.left.as_ref(), x.rows.as_ref()),
                    (x.right.as_ref(), x.cols.as_ref()),
                ]);
            }
            MatrixOperator::InnerProduct(x) => {
                dimensions.push(x.dimension.as_ref());
                vectors.extend([
                    (x.left.as_ref(), x.dimension.as_ref()),
                    (x.right.as_ref(), x.dimension.as_ref()),
                ]);
            }
            MatrixOperator::EuclideanNorm(x) => {
                dimensions.push(x.dimension.as_ref());
                vectors.push((&x.vector, x.dimension.as_ref()));
            }
            MatrixOperator::FrobeniusNorm(x) => {
                dimensions.extend([x.rows.as_ref(), x.cols.as_ref()]);
                matrices.push((&x.matrix, x.rows.as_ref(), x.cols.as_ref()));
            }
            MatrixOperator::Determinant(_)
            | MatrixOperator::Trace(_)
            | MatrixOperator::ZeroMatrix(_)
            | MatrixOperator::IdentityMatrix(_)
            | MatrixOperator::Transpose(_)
            | MatrixOperator::ConjugateTranspose(_) => {
                unreachable!("foundation WD has its own branches")
            }
        }
        for dimension in dimensions {
            domains.push((dimension.clone(), Obj::StandardSet(StandardSet::N)));
        }
        for (matrix, rows, cols) in matrices {
            domains.push((
                matrix.clone(),
                matrix_space(Obj::StandardSet(StandardSet::C), rows.clone(), cols.clone()),
            ));
        }
        for (vector, n) in vectors {
            domains.push((
                vector.clone(),
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: Box::new(n.clone()),
                })),
            ));
        }
        let mut requirements = Vec::new();
        for (element, set) in domains {
            let fact = AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element,
                set,
                line_file: None,
            });
            requirements.push(self.verify_required_atomic_fact(
                fact,
                state,
                "matrix operation needs its exact scalar and finite index domains".into(),
            )?);
        }
        if let MatrixOperator::Inverse(x) = value {
            let fact = AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::MatrixOperator(MatrixOperator::Determinant(Determinant {
                    matrix: x.matrix.clone(),
                    order: x.order.clone(),
                })),
                right: matrix_number(0),
                line_file: None,
            });
            requirements.push(self.verify_required_atomic_fact(
                fact,
                state,
                "matrix inverse requires a proved nonzero determinant".into(),
            )?);
        }
        Ok(self.with_requirements(children, requirements))
    }

    fn verify_matrix_dimensions(
        &mut self,
        dims: &[&Obj],
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let children = self.verify_objs_as_children(dims, state)?;
        let mut requirements = Vec::new();
        for dimension in dims {
            requirements.push(self.require_obj_in_standard_set(
                dimension,
                StandardSet::N,
                state,
                "matrix dimension must be natural".into(),
            )?);
        }
        Ok(self.with_requirements(children, requirements))
    }

    fn verify_matrix_square_operation(
        &mut self,
        matrix: &Obj,
        order: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let children = self.verify_objs_as_children(&[matrix, order], state)?;
        let natural = self.require_obj_in_standard_set(
            order,
            StandardSet::N,
            state,
            "matrix order must be natural".into(),
        )?;
        let fact = self.native_matrix_membership(matrix, StandardSet::C, order, order);
        let square = self.verify_required_atomic_fact(
            fact,
            state,
            "operation needs its complete square matrix domain".into(),
        )?;
        Ok(self.with_requirements(children, vec![natural, square]))
    }

    fn verify_matrix_rectangular_operation(
        &mut self,
        matrix: &Obj,
        rows: &Obj,
        cols: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let children = self.verify_objs_as_children(&[matrix, rows, cols], state)?;
        let mut requirements = vec![
            self.require_obj_in_standard_set(
                rows,
                StandardSet::N,
                state,
                "matrix rows must be natural".into(),
            )?,
            self.require_obj_in_standard_set(
                cols,
                StandardSet::N,
                state,
                "matrix columns must be natural".into(),
            )?,
        ];
        let fact = self.native_matrix_membership(matrix, StandardSet::C, rows, cols);
        requirements.push(self.verify_required_atomic_fact(
            fact,
            state,
            "operation needs its complete complex matrix domain".into(),
        )?);
        Ok(self.with_requirements(children, requirements))
    }
}

fn matrix_index_set(end: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(crate::execute::execute_fact_stmt::native_matrix::matrix_number(1)),
        end: Box::new(end.clone()),
    }))
}
