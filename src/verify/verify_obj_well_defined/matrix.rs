use crate::prelude::*;

impl Runtime {
    /// Mathematical contract: a finite interval literal is meaningful when
    /// both endpoints are well-defined real numbers; endpoint order may
    /// describe an empty interval and is not a definedness condition.
    pub(in crate::verify) fn verify_interval_obj_well_defined(
        &mut self,
        x: &IntervalObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(x.start(), verify_state)?;
        self.verify_obj_well_defined_and_store_cache(x.end(), verify_state)?;
        self.require_obj_in_r(x.start(), verify_state)?;
        self.require_obj_in_r(x.end(), verify_state)?;
        Ok(())
    }

    /// Mathematical contract: a one-sided infinite interval is meaningful
    /// when its finite endpoint is a well-defined real number.
    pub(in crate::verify) fn verify_one_side_infinity_interval_obj_well_defined(
        &mut self,
        x: &OneSideInfinityIntervalObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(x.start(), verify_state)?;
        self.require_obj_in_r(x.start(), verify_state)?;
        Ok(())
    }

    /// Mathematical contract: `finite_seq_set(S,n)` requires a well-defined
    /// set carrier `S` and a natural-number length `n`, including zero.
    pub(in crate::verify) fn verify_finite_seq_set_well_defined(
        &mut self,
        x: &FiniteSeqSet,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.n, verify_state)?;
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
    pub(in crate::verify) fn verify_seq_set_well_defined(
        &mut self,
        x: &SeqSet,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
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
    pub(in crate::verify) fn verify_finite_seq_list_obj_well_defined(
        &mut self,
        x: &FiniteSeqListObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        for o in x.objs.iter() {
            self.verify_obj_well_defined_and_store_cache(o, verify_state)?;
        }
        Ok(())
    }

    /// Mathematical contract: `matrix(S,m,n)` requires a well-defined set of
    /// entries and positive-integer row and column counts.
    pub(in crate::verify) fn verify_matrix_set_well_defined(
        &mut self,
        x: &MatrixSet,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.row_len, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.col_len, verify_state)?;
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
    pub(in crate::verify) fn verify_matrix_list_obj_well_defined(
        &mut self,
        x: &MatrixListObj,
        verify_state: &UseContextVerifyState,
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
        for row in x.rows.iter() {
            for o in row.iter() {
                self.verify_obj_well_defined_and_store_cache(o, verify_state)?;
            }
        }
        Ok(())
    }

    /// Mathematical contract: matrix addition requires two real matrices with
    /// equal row and column dimensions.
    pub(in crate::verify) fn verify_matrix_add_well_defined(
        &mut self,
        ma: &MatrixAdd,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ma.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ma.right, verify_state)?;
        let left = self.real_matrix_type(&ma.left, verify_state, MATRIX_ADD)?;
        let right = self.real_matrix_type(&ma.right, verify_state, MATRIX_ADD)?;
        self.require_same_matrix_dimension(&left.row_len, &right.row_len, "row", MATRIX_ADD)?;
        self.require_same_matrix_dimension(&left.col_len, &right.col_len, "column", MATRIX_ADD)?;
        Ok(())
    }

    /// Mathematical contract: matrix subtraction requires two real matrices
    /// with equal row and column dimensions.
    pub(in crate::verify) fn verify_matrix_sub_well_defined(
        &mut self,
        ms: &MatrixSub,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ms.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ms.right, verify_state)?;
        let left = self.real_matrix_type(&ms.left, verify_state, MATRIX_SUB)?;
        let right = self.real_matrix_type(&ms.right, verify_state, MATRIX_SUB)?;
        self.require_same_matrix_dimension(&left.row_len, &right.row_len, "row", MATRIX_SUB)?;
        self.require_same_matrix_dimension(&left.col_len, &right.col_len, "column", MATRIX_SUB)?;
        Ok(())
    }

    /// Mathematical contract: matrix multiplication requires real matrices
    /// whose left column count equals the right row count.
    pub(in crate::verify) fn verify_matrix_mul_well_defined(
        &mut self,
        mm: &MatrixMul,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&mm.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mm.right, verify_state)?;
        let left = self.real_matrix_type(&mm.left, verify_state, MATRIX_MUL)?;
        let right = self.real_matrix_type(&mm.right, verify_state, MATRIX_MUL)?;
        self.require_same_matrix_dimension(&left.col_len, &right.row_len, "inner", MATRIX_MUL)?;
        Ok(())
    }

    /// Mathematical contract: matrix scalar multiplication requires a real
    /// scalar and a real matrix of known dimensions.
    pub(in crate::verify) fn verify_matrix_scalar_mul_well_defined(
        &mut self,
        m: &MatrixScalarMul,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.scalar, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.matrix, verify_state)?;
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
    pub(in crate::verify) fn verify_matrix_pow_well_defined(
        &mut self,
        m: &MatrixPow,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.exponent, verify_state)?;
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
    pub(crate) fn real_matrix_type(
        &mut self,
        obj: &Obj,
        verify_state: &UseContextVerifyState,
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
            .verify_objs_are_equal_by_known_equality(&result.set, &real, default_line_file())
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
            .verify_objs_are_equal_by_known_equality(left, right, default_line_file())
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
    /// Mathematical contract: a literal matrix has a unique `(rows,columns)`
    /// shape only when every row has the same length.
    pub(in crate::verify) fn rectangular_shape_of_matrix_list_obj(
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
}
