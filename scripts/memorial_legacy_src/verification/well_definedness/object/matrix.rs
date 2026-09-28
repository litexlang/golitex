//! Matrix, sequence, and interval object well-definedness.

use crate::prelude::*;

impl Runtime {
    fn push_matrix_wd_fact_check(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        fact: &AtomicFact,
        verify_state: &VerifyState,
        error_message: String,
    ) -> Result<(), RuntimeError> {
        let result = self.verify_atomic_fact(fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(error_message),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(result)?);
        Ok(())
    }

    pub(in crate::verification) fn verify_interval_obj_well_defined_result(
        &mut self,
        value: &IntervalObj,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [value.start(), value.end()].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
            self.push_required_real_object_wd_result(&mut steps, child, verify_state)?;
        }
        Ok(steps)
    }

    pub(in crate::verification) fn verify_one_side_infinity_interval_obj_well_defined_result(
        &mut self,
        value: &OneSideInfinityIntervalObj,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            value.start(),
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?);
        self.push_required_real_object_wd_result(&mut steps, value.start(), verify_state)?;
        Ok(steps)
    }

    pub(in crate::verification) fn verify_finite_seq_set_well_defined_result(
        &mut self,
        value: &FiniteSeqSet,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.set, &value.n].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let is_set: AtomicFact = self
            .new_is_set_fact((*value.set).clone(), default_line_file())
            .into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &is_set,
            verify_state,
            format!("finite_seq_set: first argument {} is not a set", value.set),
        )?;
        let length: AtomicFact = self
            .new_in_fact(
                (*value.n).clone(),
                StandardSet::N.into(),
                default_line_file(),
            )
            .into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &length,
            verify_state,
            format!(
                "finite_seq_set: length argument {} is not verified in N",
                value.n
            ),
        )?;
        Ok(steps)
    }

    pub(in crate::verification) fn verify_seq_set_well_defined_result(
        &mut self,
        value: &SeqSet,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &value.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?);
        let is_set: AtomicFact = self
            .new_is_set_fact((*value.set).clone(), default_line_file())
            .into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &is_set,
            verify_state,
            format!("seq: argument {} is not a set", value.set),
        )?;
        Ok(steps)
    }

    pub(in crate::verification) fn verify_finite_seq_list_obj_well_defined_result(
        &mut self,
        value: &FiniteSeqListObj,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in value.objs.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        Ok(steps)
    }

    pub(in crate::verification) fn verify_matrix_set_well_defined_result(
        &mut self,
        value: &MatrixSet,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.set, &value.row_len, &value.col_len]
            .into_iter()
            .enumerate()
        {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let is_set: AtomicFact = self
            .new_is_set_fact((*value.set).clone(), default_line_file())
            .into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &is_set,
            verify_state,
            format!("matrix: first argument {} is not a set", value.set),
        )?;
        for (label, dimension) in [
            ("row_len", value.row_len.as_ref()),
            ("col_len", value.col_len.as_ref()),
        ] {
            let positive: AtomicFact = self
                .new_in_fact(
                    dimension.clone(),
                    StandardSet::NPos.into(),
                    default_line_file(),
                )
                .into();
            self.push_matrix_wd_fact_check(
                &mut steps,
                &positive,
                verify_state,
                format!("matrix: {label} argument {dimension} is not verified in N+"),
            )?;
        }
        Ok(steps)
    }

    pub(in crate::verification) fn verify_matrix_list_obj_well_defined_result(
        &mut self,
        value: &MatrixListObj,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        if value.rows.is_empty() || value.rows[0].is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "matrix literal must have at least one row and one column".to_string(),
                ),
            )));
        }
        let column_count = value.rows[0].len();
        for row in &value.rows {
            if row.len() != column_count {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix literal: row length {} differs from first row length {}",
                        row.len(),
                        column_count
                    )),
                )));
            }
        }
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for child in value.rows.iter().flat_map(|row| row.iter()) {
            let argument_index = steps.children.len();
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        Ok(steps)
    }

    fn push_known_matrix_equality_result(
        &self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        left: &Obj,
        right: &Obj,
        error_message: String,
    ) -> Result<(), RuntimeError> {
        let result = self.verify_equal_fact_by_known_equality(&self.new_equal_fact_from_refs(
            left,
            right,
            default_line_file(),
        ));
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(error_message),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check_after_structural_wd(result)?);
        Ok(())
    }

    fn require_same_matrix_dimension_result(
        &self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        left: &Obj,
        right: &Obj,
        dimension: &str,
        operator: &str,
    ) -> Result<(), RuntimeError> {
        self.push_known_matrix_equality_result(
            steps,
            left,
            right,
            format!(
                "matrix {operator} shapes do not match: {dimension} dimensions are {left} and {right}"
            ),
        )
    }

    fn real_matrix_type_result(
        &mut self,
        steps: &mut SuccessVerifyObjWellDefinedStepsResult,
        object: &Obj,
        verify_state: &VerifyState,
        operator: &str,
    ) -> Result<MatrixSet, RuntimeError> {
        let result = match object {
            Obj::MatrixListObj(matrix) => {
                let (rows, columns) = Self::rectangular_shape_of_matrix_list_obj(matrix)?;
                if rows == 0 || columns == 0 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "matrix literal must have at least one row and one column".to_string(),
                        ),
                    )));
                }
                for cell in matrix.rows.iter().flat_map(|row| row.iter()) {
                    self.push_required_real_object_wd_result(steps, cell, verify_state)
                        .map_err(|_| {
                            RuntimeError::from(WellDefinedRuntimeError(
                                RuntimeErrorStruct::new_with_just_msg(format!(
                                    "matrix {operator} requires entries in R; {cell} is not verified in R"
                                )),
                            ))
                        })?;
                }
                MatrixSet::new(
                    StandardSet::R.into(),
                    Number::new(rows.to_string()).into(),
                    Number::new(columns.to_string()).into(),
                )
            }
            Obj::MatrixAdd(value) => {
                let left =
                    self.real_matrix_type_result(steps, &value.left, verify_state, MATRIX_ADD)?;
                let right =
                    self.real_matrix_type_result(steps, &value.right, verify_state, MATRIX_ADD)?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &left.row_len,
                    &right.row_len,
                    "row",
                    MATRIX_ADD,
                )?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &left.col_len,
                    &right.col_len,
                    "column",
                    MATRIX_ADD,
                )?;
                left
            }
            Obj::MatrixSub(value) => {
                let left =
                    self.real_matrix_type_result(steps, &value.left, verify_state, MATRIX_SUB)?;
                let right =
                    self.real_matrix_type_result(steps, &value.right, verify_state, MATRIX_SUB)?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &left.row_len,
                    &right.row_len,
                    "row",
                    MATRIX_SUB,
                )?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &left.col_len,
                    &right.col_len,
                    "column",
                    MATRIX_SUB,
                )?;
                left
            }
            Obj::MatrixMul(value) => {
                let left =
                    self.real_matrix_type_result(steps, &value.left, verify_state, MATRIX_MUL)?;
                let right =
                    self.real_matrix_type_result(steps, &value.right, verify_state, MATRIX_MUL)?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &left.col_len,
                    &right.row_len,
                    "inner",
                    MATRIX_MUL,
                )?;
                MatrixSet::new(
                    StandardSet::R.into(),
                    (*left.row_len).clone(),
                    (*right.col_len).clone(),
                )
            }
            Obj::MatrixScalarMul(value) => {
                self.push_required_real_object_wd_result(steps, &value.scalar, verify_state)
                    .map_err(|_| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(format!(
                                "matrix {MATRIX_SCALAR_MUL} requires scalar {} in R",
                                value.scalar
                            )),
                        ))
                    })?;
                self.real_matrix_type_result(steps, &value.matrix, verify_state, MATRIX_SCALAR_MUL)?
            }
            Obj::MatrixPow(value) => {
                let base =
                    self.real_matrix_type_result(steps, &value.base, verify_state, MATRIX_POW)?;
                self.require_same_matrix_dimension_result(
                    steps,
                    &base.row_len,
                    &base.col_len,
                    "square",
                    MATRIX_POW,
                )?;
                base
            }
            _ => {
                let matrix_set = self.get_matrix_set_for_obj(object).ok_or_else(|| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix {operator} requires a matrix(R, m, n) operand; {object} has no known matrix type"
                        )),
                    ))
                })?;
                let membership: AtomicFact = self
                    .new_in_fact(
                        object.clone(),
                        matrix_set.clone().into(),
                        default_line_file(),
                    )
                    .into();
                let membership_result = self.verify_atomic_fact(&membership, verify_state)?;
                if membership_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix {operator} cannot retain the known matrix type of operand {object}"
                        )),
                    )));
                }
                steps.push_fact_check(super::success_obj_fact_check(membership_result)?);
                matrix_set
            }
        };

        let real: Obj = StandardSet::R.into();
        self.push_known_matrix_equality_result(
            steps,
            &result.set,
            &real,
            format!(
                "matrix {operator} requires entries in R; operand {object} has entries in {}",
                result.set
            ),
        )?;
        Ok(result)
    }

    fn verify_binary_matrix_operator_result(
        &mut self,
        left_object: &Obj,
        right_object: &Obj,
        operator: &str,
        dimension_pairs: impl for<'a> FnOnce(
            &'a MatrixSet,
            &'a MatrixSet,
        ) -> Vec<(&'a Obj, &'a Obj, &'static str)>,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [left_object, right_object].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let left = self.real_matrix_type_result(&mut steps, left_object, verify_state, operator)?;
        let right =
            self.real_matrix_type_result(&mut steps, right_object, verify_state, operator)?;
        for (left_dimension, right_dimension, label) in dimension_pairs(&left, &right) {
            self.require_same_matrix_dimension_result(
                &mut steps,
                left_dimension,
                right_dimension,
                label,
                operator,
            )?;
        }
        Ok(steps)
    }

    pub(in crate::verification) fn verify_matrix_add_well_defined_result(
        &mut self,
        value: &MatrixAdd,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_binary_matrix_operator_result(
            &value.left,
            &value.right,
            MATRIX_ADD,
            |left, right| {
                vec![
                    (&left.row_len, &right.row_len, "row"),
                    (&left.col_len, &right.col_len, "column"),
                ]
            },
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_matrix_sub_well_defined_result(
        &mut self,
        value: &MatrixSub,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_binary_matrix_operator_result(
            &value.left,
            &value.right,
            MATRIX_SUB,
            |left, right| {
                vec![
                    (&left.row_len, &right.row_len, "row"),
                    (&left.col_len, &right.col_len, "column"),
                ]
            },
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_matrix_mul_well_defined_result(
        &mut self,
        value: &MatrixMul,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        self.verify_binary_matrix_operator_result(
            &value.left,
            &value.right,
            MATRIX_MUL,
            |left, right| vec![(&left.col_len, &right.row_len, "inner")],
            verify_state,
        )
    }

    pub(in crate::verification) fn verify_matrix_scalar_mul_well_defined_result(
        &mut self,
        value: &MatrixScalarMul,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.scalar, &value.matrix].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        self.push_required_real_object_wd_result(&mut steps, &value.scalar, verify_state)
            .map_err(|_| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix {MATRIX_SCALAR_MUL} requires scalar {} in R",
                        value.scalar
                    )),
                ))
            })?;
        self.real_matrix_type_result(&mut steps, &value.matrix, verify_state, MATRIX_SCALAR_MUL)?;
        Ok(steps)
    }

    pub(in crate::verification) fn verify_matrix_pow_well_defined_result(
        &mut self,
        value: &MatrixPow,
        verify_state: &VerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, child) in [&value.base, &value.exponent].into_iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                child,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        let base =
            self.real_matrix_type_result(&mut steps, &value.base, verify_state, MATRIX_POW)?;
        self.require_same_matrix_dimension_result(
            &mut steps,
            &base.row_len,
            &base.col_len,
            "square",
            MATRIX_POW,
        )?;
        let positive: AtomicFact = self
            .new_in_fact(
                (*value.exponent).clone(),
                StandardSet::NPos.into(),
                default_line_file(),
            )
            .into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &positive,
            verify_state,
            format!(
                "matrix {MATRIX_POW}: exponent {} is not verified in N+",
                value.exponent
            ),
        )?;
        Ok(steps)
    }

    /// Mathematical contract: a literal matrix has a unique `(rows,columns)`
    /// shape only when every row has the same length.
    pub(in crate::verification) fn rectangular_shape_of_matrix_list_obj(
        m: &MatrixListObj,
    ) -> Result<(usize, usize), RuntimeError> {
        let rows = m.rows.len();
        let cols = if rows == 0 { 0 } else { m.rows[0].len() };
        for row in m.rows.iter() {
            if row.len() != cols {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(
                        "matrix list is not rectangular (row lengths differ)".to_string(),
                    ),
                )));
            }
        }
        Ok((rows, cols))
    }

    /// Read the result carrier of an already well-defined real-matrix object.
    /// All membership, entry-carrier, and dimension obligations belong to the
    /// object's WD Result; this representation query performs no verification
    /// and therefore cannot manufacture or discard proof evidence.
    pub fn real_matrix_type_after_well_defined(
        &self,
        object: &Obj,
        operator: &str,
    ) -> Result<MatrixSet, RuntimeError> {
        let result = match object {
            Obj::MatrixListObj(matrix) => {
                let (rows, columns) = Self::rectangular_shape_of_matrix_list_obj(matrix)?;
                if rows == 0 || columns == 0 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "matrix literal must have at least one row and one column".to_string(),
                        ),
                    )));
                }
                MatrixSet::new(
                    StandardSet::R.into(),
                    Number::new(rows.to_string()).into(),
                    Number::new(columns.to_string()).into(),
                )
            }
            Obj::MatrixAdd(value) => {
                self.real_matrix_type_after_well_defined(&value.left, MATRIX_ADD)?
            }
            Obj::MatrixSub(value) => {
                self.real_matrix_type_after_well_defined(&value.left, MATRIX_SUB)?
            }
            Obj::MatrixMul(value) => {
                let left =
                    self.real_matrix_type_after_well_defined(&value.left, MATRIX_MUL)?;
                let right =
                    self.real_matrix_type_after_well_defined(&value.right, MATRIX_MUL)?;
                MatrixSet::new(
                    StandardSet::R.into(),
                    (*left.row_len).clone(),
                    (*right.col_len).clone(),
                )
            }
            Obj::MatrixScalarMul(value) => self
                .real_matrix_type_after_well_defined(&value.matrix, MATRIX_SCALAR_MUL)?,
            Obj::MatrixPow(value) => {
                self.real_matrix_type_after_well_defined(&value.base, MATRIX_POW)?
            }
            _ => self.get_matrix_set_for_obj(object).ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix {operator} requires a matrix(R, m, n) operand; {object} has no known matrix type"
                    )),
                ))
            })?,
        };

        if !objs_equal_with_nested_binder_alpha_equivalence(&result.set, &Obj::from(StandardSet::R))
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {operator} requires entries in R; operand {object} has entries in {}",
                    result.set
                )),
            )));
        }
        Ok(result)
    }
}
