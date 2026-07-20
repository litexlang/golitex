use crate::prelude::*;

impl Runtime {
    pub(in crate::verify) fn verify_interval_obj_well_defined(
        &mut self,
        x: &IntervalObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(x.start(), verify_state)?;
        self.verify_obj_well_defined_and_store_cache(x.end(), verify_state)?;
        self.require_obj_in_r(x.start(), verify_state)?;
        self.require_obj_in_r(x.end(), verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_one_side_infinity_interval_obj_well_defined(
        &mut self,
        x: &OneSideInfinityIntervalObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(x.start(), verify_state)?;
        self.require_obj_in_r(x.start(), verify_state)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_finite_seq_set_well_defined(
        &mut self,
        x: &FiniteSeqSet,
        verify_state: &VerifyState,
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
        let n_in_n_pos = InFact::new(
            (*x.n).clone(),
            StandardSet::NPos.into(),
            default_line_file(),
        )
        .into();
        let n_ok = self.verify_atomic_fact(&n_in_n_pos, verify_state)?;
        if n_ok.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "finite_seq_set: length argument {} is not verified in N_pos",
                    x.n
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_seq_set_well_defined(
        &mut self,
        x: &SeqSet,
        verify_state: &VerifyState,
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

    pub(in crate::verify) fn verify_finite_seq_list_obj_well_defined(
        &mut self,
        x: &FiniteSeqListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for o in x.objs.iter() {
            self.verify_obj_well_defined_and_store_cache(o, verify_state)?;
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_set_well_defined(
        &mut self,
        x: &MatrixSet,
        verify_state: &VerifyState,
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
                        "matrix: {} argument {} is not verified in N_pos",
                        label, len_obj
                    )),
                )));
            }
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_list_obj_well_defined(
        &mut self,
        x: &MatrixListObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
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

    pub(in crate::verify) fn verify_matrix_add_well_defined(
        &mut self,
        ma: &MatrixAdd,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ma.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ma.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &ma.left)?;
        let shape_right = Self::matrix_value_shape(self, &ma.right)?;
        if shape_left != shape_right {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {}: shape {:?} and {:?} do not match",
                    MATRIX_ADD, shape_left, shape_right
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_sub_well_defined(
        &mut self,
        ms: &MatrixSub,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&ms.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&ms.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &ms.left)?;
        let shape_right = Self::matrix_value_shape(self, &ms.right)?;
        if shape_left != shape_right {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {}: shape {:?} and {:?} do not match",
                    MATRIX_SUB, shape_left, shape_right
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_mul_well_defined(
        &mut self,
        mm: &MatrixMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&mm.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mm.right, verify_state)?;
        let shape_left = Self::matrix_value_shape(self, &mm.left)?;
        let shape_right = Self::matrix_value_shape(self, &mm.right)?;
        if shape_left.1 != shape_right.0 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {}: left columns {} != right rows {}",
                    MATRIX_MUL, shape_left.1, shape_right.0
                )),
            )));
        }
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_scalar_mul_well_defined(
        &mut self,
        m: &MatrixScalarMul,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.scalar, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.matrix, verify_state)?;
        let _ = Self::matrix_value_shape(self, &m.matrix)?;
        Ok(())
    }

    pub(in crate::verify) fn verify_matrix_pow_well_defined(
        &mut self,
        m: &MatrixPow,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&m.base, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.exponent, verify_state)?;
        let shape_base = Self::matrix_value_shape(self, &m.base)?;
        if shape_base.0 != shape_base.1 {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix {}: base must be square, got {}x{}",
                    MATRIX_POW, shape_base.0, shape_base.1
                )),
            )));
        }
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
                    "matrix {}: exponent {} is not verified in N_pos",
                    MATRIX_POW, m.exponent
                )),
            )));
        }
        Ok(())
    }

    /// Dimensions of a matrix-valued expression (literal, known name, or matrix operators).
    pub(in crate::verify) fn matrix_value_shape(
        rt: &Runtime,
        obj: &Obj,
    ) -> Result<(usize, usize), RuntimeError> {
        match obj {
            Obj::MatrixListObj(m) => Self::rectangular_shape_of_matrix_list_obj(m),
            Obj::Atom(AtomObj::Identifier(id)) => {
                Self::matrix_list_shape_for_name_known_as_matrix_list(rt, &id.name)
            }
            Obj::MatrixAdd(inner) => Self::matrix_value_shape(rt, &inner.left),
            Obj::MatrixSub(inner) => Self::matrix_value_shape(rt, &inner.left),
            Obj::MatrixMul(inner) => {
                let sl = Self::matrix_value_shape(rt, &inner.left)?;
                let sr = Self::matrix_value_shape(rt, &inner.right)?;
                if sl.1 != sr.0 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix {}: left columns {} != right rows {}",
                            MATRIX_MUL, sl.1, sr.0
                        )),
                    )));
                }
                Ok((sl.0, sr.1))
            }
            Obj::MatrixScalarMul(inner) => Self::matrix_value_shape(rt, &inner.matrix),
            Obj::MatrixPow(inner) => {
                let s = Self::matrix_value_shape(rt, &inner.base)?;
                if s.0 != s.1 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "matrix {}: base must be square, got {}x{}",
                            MATRIX_POW, s.0, s.1
                        )),
                    )));
                }
                Ok(s)
            }
            _ => Self::matrix_list_shape_for_name_known_as_matrix_list(rt, &obj.to_string()),
        }
    }

    /// Shape of a matrix list stored under `key` in `known_objs_equal_to_matrix_list`.
    /// When the entry carries a `MatrixSet`, resolved `row_len` / `col_len` must match the list shape.
    pub(in crate::verify) fn matrix_list_shape_for_name_known_as_matrix_list(
        rt: &Runtime,
        key: &str,
    ) -> Result<(usize, usize), RuntimeError> {
        let Some(known) = rt.get_obj_equal_to_matrix_list(key) else {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "`{}` is not known as a matrix list value",
                    key
                )),
            )));
        };
        let shape = Self::rectangular_shape_of_matrix_list_obj(&known)?;
        if let Some(ms) = rt.get_matrix_set_for_obj_equal_to_matrix_list(key) {
            Self::ensure_matrix_list_matches_matrix_set(rt, &known, &ms)?;
        }
        Ok(shape)
    }

    pub(in crate::verify) fn ensure_matrix_list_matches_matrix_set(
        rt: &Runtime,
        m: &MatrixListObj,
        ms: &MatrixSet,
    ) -> Result<(), RuntimeError> {
        let (rows, cols) = Self::rectangular_shape_of_matrix_list_obj(m)?;
        let row_expect = rt
            .resolve_obj_to_number(ms.row_len.as_ref())
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: cannot resolve row_len {} of matrix type for list shape check",
                        ms.row_len
                    )),
                ))
            })?;
        let col_expect = rt
            .resolve_obj_to_number(ms.col_len.as_ref())
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "matrix: cannot resolve col_len {} of matrix type for list shape check",
                        ms.col_len
                    )),
                ))
            })?;
        let r = row_expect.normalized_value.parse::<usize>().map_err(|_| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: row_len `{}` is not a valid size",
                    row_expect.normalized_value
                )),
            ))
        })?;
        let c = col_expect.normalized_value.parse::<usize>().map_err(|_| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix: col_len `{}` is not a valid size",
                    col_expect.normalized_value
                )),
            ))
        })?;
        if r != rows || c != cols {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "matrix list has shape {}x{} but matrix type expects {}x{}",
                    rows, cols, r, c
                )),
            )));
        }
        Ok(())
    }

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
