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
        let is_set: AtomicFact = IsSetFact::new((*value.set).clone(), default_line_file()).into();
        self.push_matrix_wd_fact_check(
            &mut steps,
            &is_set,
            verify_state,
            format!("finite_seq_set: first argument {} is not a set", value.set),
        )?;
        let length: AtomicFact = InFact::new(
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
        let is_set: AtomicFact = IsSetFact::new((*value.set).clone(), default_line_file()).into();
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
        let is_set: AtomicFact = IsSetFact::new((*value.set).clone(), default_line_file()).into();
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
            let positive: AtomicFact = InFact::new(
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
        let result = self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
            left,
            right,
            default_line_file(),
        ));
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(error_message),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(result)?);
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
                let membership: AtomicFact = InFact::new(
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
        let positive: AtomicFact = InFact::new(
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

    /// Mathematical contract: a finite interval literal is meaningful when
    /// both endpoints are well-defined real numbers; endpoint order may
    /// describe an empty interval and is not a definedness condition.
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

    /// Mathematical contract: a finite interval literal is meaningful when
    /// both endpoints are well-defined real numbers; endpoint order may
    /// describe an empty interval and is not a definedness condition.
    pub(in crate::verification) fn verify_interval_obj_well_defined(
        &mut self,
        x: &IntervalObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            x.start(),
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            x.end(),
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_r(x.start(), verify_state)?;
        self.require_obj_in_r(x.end(), verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a one-sided infinite interval is meaningful
    /// when its finite endpoint is a well-defined real number.
    pub(in crate::verification) fn verify_one_side_infinity_interval_obj_well_defined(
        &mut self,
        x: &OneSideInfinityIntervalObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            x.start(),
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.require_obj_in_r(x.start(), verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `finite_seq_set(S,n)` requires a well-defined
    /// set carrier `S` and a natural-number length `n`, including zero.
    pub(in crate::verification) fn verify_finite_seq_set_well_defined(
        &mut self,
        x: &FiniteSeqSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.n,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_seq_set: first argument {} is not a set",
                    x.set
                )),
            )));
        }
        let n_in_n = InFact::new((*x.n).clone(), StandardSet::N.into(), default_line_file()).into();
        let n_ok = self.verify_atomic_fact(&n_in_n, verify_state)?;
        if n_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_seq_set: length argument {} is not verified in N",
                    x.n
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: an infinite sequence carrier is meaningful when
    /// its codomain is a well-defined object provably known to be a set.
    pub(in crate::verification) fn verify_seq_set_well_defined(
        &mut self,
        x: &SeqSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "seq: argument {} is not a set",
                    x.set
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: every value in a finite sequence literal is a
    /// well-defined object; the empty literal is the sequence of length zero.
    pub(in crate::verification) fn verify_finite_seq_list_obj_well_defined(
        &mut self,
        x: &FiniteSeqListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for (argument_index, o) in x.objs.iter().enumerate() {
            self.verify_child_obj_well_defined_and_store_cache(
                o,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?;
        }
        Ok(())
    }

    /// Mathematical contract: `matrix(S,m,n)` requires a well-defined set of
    /// entries and positive-integer row and column counts.
    pub(in crate::verification) fn verify_matrix_set_well_defined(
        &mut self,
        x: &MatrixSet,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &x.set,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.row_len,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &x.col_len,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 2 },
        )?;
        let is_set_fact = IsSetFact::new((*x.set).clone(), default_line_file()).into();
        let set_ok = self.verify_atomic_fact(&is_set_fact, verify_state)?;
        if set_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: first argument {} is not a set",
                    x.set
                )),
            )));
        }
        for (label, len_obj) in [("row_len", &x.row_len), ("col_len", &x.col_len)] {
            let in_n_pos = InFact::new(
                (**len_obj).clone(),
                StandardSet::NPos.into(),
                default_line_file(),
            )
            .into();
            let ok = self.verify_atomic_fact(&in_n_pos, verify_state)?;
            if ok.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: {} argument {} is not verified in N+",
                        label, len_obj
                    )),
                )));
            }
        }
        Ok(())
    }

    /// Mathematical contract: a matrix literal is a nonempty rectangular
    /// array and every cell is a well-defined object.
    pub(in crate::verification) fn verify_matrix_list_obj_well_defined(
        &mut self,
        x: &MatrixListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        if x.rows.is_empty() || x.rows[0].is_empty() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "matrix literal must have at least one row and one column".to_string(),
                ),
            )));
        }
        if !x.rows.is_empty() {
            let col_len = x.rows[0].len();
            for row in x.rows.iter() {
                if row.len() != col_len {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix literal: row length {} differs from first row length {}",
                            row.len(),
                            col_len
                        )),
                    )));
                }
            }
        }
        let mut argument_index = 0;
        for row in x.rows.iter() {
            for o in row.iter() {
                self.verify_child_obj_well_defined_and_store_cache(
                    o,
                    verify_state,
                    WellDefinedObjChildRole::ConstructorArgument { argument_index },
                )?;
                argument_index += 1;
            }
        }
        Ok(())
    }

    /// Mathematical contract: matrix addition requires two real matrices with
    /// equal row and column dimensions.
    pub(in crate::verification) fn verify_matrix_add_well_defined(
        &mut self,
        ma: &MatrixAdd,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &ma.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &ma.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let left = self.real_matrix_type(&ma.left, verify_state, MATRIX_ADD)?;
        let right = self.real_matrix_type(&ma.right, verify_state, MATRIX_ADD)?;
        self.require_same_matrix_dimension(&left.row_len, &right.row_len, "row", MATRIX_ADD)?;
        self.require_same_matrix_dimension(&left.col_len, &right.col_len, "column", MATRIX_ADD)?;
        Ok(())
    }

    /// Mathematical contract: matrix subtraction requires two real matrices
    /// with equal row and column dimensions.
    pub(in crate::verification) fn verify_matrix_sub_well_defined(
        &mut self,
        ms: &MatrixSub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &ms.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &ms.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let left = self.real_matrix_type(&ms.left, verify_state, MATRIX_SUB)?;
        let right = self.real_matrix_type(&ms.right, verify_state, MATRIX_SUB)?;
        self.require_same_matrix_dimension(&left.row_len, &right.row_len, "row", MATRIX_SUB)?;
        self.require_same_matrix_dimension(&left.col_len, &right.col_len, "column", MATRIX_SUB)?;
        Ok(())
    }

    /// Mathematical contract: matrix multiplication requires real matrices
    /// whose left column count equals the right row count.
    pub(in crate::verification) fn verify_matrix_mul_well_defined(
        &mut self,
        mm: &MatrixMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &mm.left,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &mm.right,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let left = self.real_matrix_type(&mm.left, verify_state, MATRIX_MUL)?;
        let right = self.real_matrix_type(&mm.right, verify_state, MATRIX_MUL)?;
        self.require_same_matrix_dimension(&left.col_len, &right.row_len, "inner", MATRIX_MUL)?;
        Ok(())
    }

    /// Mathematical contract: matrix scalar multiplication requires a real
    /// scalar and a real matrix of known dimensions.
    pub(in crate::verification) fn verify_matrix_scalar_mul_well_defined(
        &mut self,
        m: &MatrixScalarMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &m.scalar,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &m.matrix,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        self.require_obj_in_r(&m.scalar, verify_state)
            .map_err(|_| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix {} requires scalar {} in R",
                        MATRIX_SCALAR_MUL, m.scalar
                    )),
                ))
            })?;
        let _ = self.real_matrix_type(&m.matrix, verify_state, MATRIX_SCALAR_MUL)?;
        Ok(())
    }

    /// Mathematical contract: matrix exponentiation requires a square real
    /// matrix and a positive-integer exponent.
    pub(in crate::verification) fn verify_matrix_pow_well_defined(
        &mut self,
        m: &MatrixPow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_child_obj_well_defined_and_store_cache(
            &m.base,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?;
        self.verify_child_obj_well_defined_and_store_cache(
            &m.exponent,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?;
        let base = self.real_matrix_type(&m.base, verify_state, MATRIX_POW)?;
        self.require_same_matrix_dimension(&base.row_len, &base.col_len, "square", MATRIX_POW)?;
        let exp_in_n_pos = InFact::new(
            (*m.exponent).clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let ok = self.verify_atomic_fact(&exp_in_n_pos, verify_state)?;
        if ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {}: exponent {} is not verified in N+",
                    MATRIX_POW, m.exponent
                )),
            )));
        }
        Ok(())
    }

    /// Mathematical contract: return the formal `matrix(R,m,n)` type only for
    /// an expression whose matrix shape is known and whose entries are real.
    ///
    /// This is the well-definedness boundary for real matrix algebra. For example,
    /// `A '+ B` is accepted only when both operands have real entries and equal dimensions.
    pub fn real_matrix_type(
        &mut self,
        obj: &Obj,
        verify_state: &VerifyState,
        operator: &str,
    ) -> Result<MatrixSet, RuntimeError> {
        let result = match obj {
            Obj::MatrixListObj(matrix) => {
                let (rows, cols) = Self::rectangular_shape_of_matrix_list_obj(matrix)?;
                if rows == 0 || cols == 0 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "matrix literal must have at least one row and one column".to_string(),
                        ),
                    )));
                }
                for row in matrix.rows.iter() {
                    for cell in row.iter() {
                        self.require_obj_in_r(cell, verify_state).map_err(|_| {
                            RuntimeError::from(WellDefinedRuntimeError(
                                RuntimeErrorStruct::new_with_just_msg(format!(
                                    "matrix {} requires entries in R; {} is not verified in R",
                                    operator, cell
                                )),
                            ))
                        })?;
                    }
                }
                MatrixSet::new(
                    StandardSet::R.into(),
                    Number::new(rows.to_string()).into(),
                    Number::new(cols.to_string()).into(),
                )
            }
            Obj::MatrixAdd(value) => {
                let left = self.real_matrix_type(&value.left, verify_state, MATRIX_ADD)?;
                let right = self.real_matrix_type(&value.right, verify_state, MATRIX_ADD)?;
                self.require_same_matrix_dimension(
                    &left.row_len,
                    &right.row_len,
                    "row",
                    MATRIX_ADD,
                )?;
                self.require_same_matrix_dimension(
                    &left.col_len,
                    &right.col_len,
                    "column",
                    MATRIX_ADD,
                )?;
                left
            }
            Obj::MatrixSub(value) => {
                let left = self.real_matrix_type(&value.left, verify_state, MATRIX_SUB)?;
                let right = self.real_matrix_type(&value.right, verify_state, MATRIX_SUB)?;
                self.require_same_matrix_dimension(
                    &left.row_len,
                    &right.row_len,
                    "row",
                    MATRIX_SUB,
                )?;
                self.require_same_matrix_dimension(
                    &left.col_len,
                    &right.col_len,
                    "column",
                    MATRIX_SUB,
                )?;
                left
            }
            Obj::MatrixMul(value) => {
                let left = self.real_matrix_type(&value.left, verify_state, MATRIX_MUL)?;
                let right = self.real_matrix_type(&value.right, verify_state, MATRIX_MUL)?;
                self.require_same_matrix_dimension(
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
                self.require_obj_in_r(&value.scalar, verify_state)
                    .map_err(|_| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(format!(
                                "matrix {} requires scalar {} in R",
                                MATRIX_SCALAR_MUL, value.scalar
                            )),
                        ))
                    })?;
                self.real_matrix_type(&value.matrix, verify_state, MATRIX_SCALAR_MUL)?
            }
            Obj::MatrixPow(value) => {
                let base = self.real_matrix_type(&value.base, verify_state, MATRIX_POW)?;
                self.require_same_matrix_dimension(
                    &base.row_len,
                    &base.col_len,
                    "square",
                    MATRIX_POW,
                )?;
                base
            }
            _ => self.get_matrix_set_for_obj(obj).ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix {} requires a matrix(R, m, n) operand; {} has no known matrix type",
                        operator, obj
                    )),
                ))
            })?,
        };

        let real: Obj = StandardSet::R.into();
        if self
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &result.set,
                &real,
                default_line_file(),
            ))
            .is_unknown()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {} requires entries in R; operand {} has entries in {}",
                    operator, obj, result.set
                )),
            )));
        }
        Ok(result)
    }

    /// Mathematical contract: a matrix shape constraint holds only when the
    /// two symbolic dimensions are provably equal in the current environment.
    fn require_same_matrix_dimension(
        &self,
        left: &Obj,
        right: &Obj,
        dimension: &str,
        operator: &str,
    ) -> Result<(), RuntimeError> {
        if self
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                left,
                right,
                default_line_file(),
            ))
            .is_unknown()
        {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {} shapes do not match: {} dimensions are {} and {}",
                    operator, dimension, left, right
                )),
            )));
        }
        Ok(())
    }
}
