//! Primary object forms dispatched from keywords and atomic tokens.

use crate::prelude::*;

impl Runtime {
    /// Parses a primary object from a keyword form or ordinary atom.
    pub(super) fn parse_primary_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let tok = tb.current()?;

        if tok == STRUCT_VIEW_PREFIX {
            return self.parse_struct_view_obj(tb);
        }
        if tok == TEMPLATE_INSTANCE_PREFIX {
            return self.parse_instantiated_template_obj(tb);
        }
        if tok == I {
            tb.skip()?;
            return Ok(ImaginaryUnit::new().into());
        }
        if tok == E {
            tb.skip()?;
            return Ok(EulerNumber::new().into());
        }
        if tok == PI {
            tb.skip()?;
            return Ok(Pi::new().into());
        }
        if tok == RE || tok == IMG || tok == C_ABS {
            let operator = tok.to_string();
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(match operator.as_str() {
                RE => RealPart::new(arg).into(),
                IMG => ImaginaryPart::new(arg).into(),
                C_ABS => ComplexAbs::new(arg).into(),
                _ => unreachable!(),
            });
        }
        if tok == ABS {
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(Abs::new(arg).into());
        }
        if tok == QUOT || tok == GCD || tok == LCM || tok == MIN || tok == MAX {
            let operator = tok.to_string();
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{operator} expects 2 arguments"),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut args = args.into_iter();
            let left = args.next().expect("native binary arity was checked");
            let right = args.next().expect("native binary arity was checked");
            return Ok(match operator.as_str() {
                QUOT => Quot::new(left, right).into(),
                GCD => Gcd::new(left, right).into(),
                LCM => Lcm::new(left, right).into(),
                MIN => Min::new(left, right).into(),
                MAX => Max::new(left, right).into(),
                _ => unreachable!(),
            });
        }
        if tok == SIN || tok == ARCSIN || tok == COS || tok == TAN || tok == COT {
            let operator = tok.to_string();
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(match operator.as_str() {
                SIN => Sin::new(arg).into(),
                ARCSIN => Arcsin::new(arg).into(),
                COS => Cos::new(arg).into(),
                TAN => Tan::new(arg).into(),
                COT => Cot::new(arg).into(),
                _ => unreachable!(),
            });
        }
        if tok == SQRT {
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(Sqrt::new(arg).into());
        }
        if tok == FLOOR || tok == CEIL {
            let operator = tok.to_string();
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(if operator == FLOOR {
                Floor::new(arg).into()
            } else {
                Ceil::new(arg).into()
            });
        }
        if tok == EXP || tok == LN || tok == SIGN || tok == FACTORIAL {
            let operator = tok.to_string();
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(match operator.as_str() {
                EXP => Exp::new(arg).into(),
                LN => Ln::new(arg).into(),
                SIGN => Sign::new(arg).into(),
                FACTORIAL => Factorial::new(arg).into(),
                _ => unreachable!(),
            });
        }
        if tok == LOG {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "log expects 2 arguments (base, argument)".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let base = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "log expects 2 arguments (base, argument)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let arg = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "log expects 2 arguments (base, argument)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Log::new(base, arg).into());
        }

        // Keyword forms consume the keyword and then parse their braced objects.
        if tok == UNION {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Union::new(left, right).into());
        }
        if tok == INTERSECT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "intersect expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "intersect expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "intersect expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Intersect::new(left, right).into());
        }
        if tok == SET_MINUS {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_minus expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_minus expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_minus expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(SetMinus::new(left, right).into());
        }
        if tok == BIG_INTERSECT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "big_intersect expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "big_intersect expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(BigIntersect::new(value).into());
        }
        if tok == BIG_UNION {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "big_union expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "big_union expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(BigUnion::new(value).into());
        }
        if tok == INDEX_UNION {
            tb.skip()?;
            let mut args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "index_union expects 3 arguments (index set, ambient set, family function)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let index_set = args.remove(0);
            let ambient_set = args.remove(0);
            let family_fn = args.remove(0);
            return Ok(IndexUnion::new(index_set, ambient_set, family_fn).into());
        }
        if tok == INDEX_INTERSECT {
            tb.skip()?;
            let mut args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "index_intersect expects 3 arguments (index set, ambient set, family function)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let index_set = args.remove(0);
            let ambient_set = args.remove(0);
            let family_fn = args.remove(0);
            return Ok(IndexIntersect::new(index_set, ambient_set, family_fn).into());
        }
        if tok == PROJ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "proj expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "proj expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "proj expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Proj::new(left, right).into());
        }
        if tok == RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Range::new(left, right).into());
        }
        if tok == CLOSED_RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "closed_range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "closed_range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "closed_range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(ClosedRange::new(left, right).into());
        }
        if tok == FINITE_SEQ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_seq expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_seq expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let n = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_seq expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(FiniteSeqSet::new(set, n).into());
        }
        if tok == SEQ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "seq expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let set = args.into_iter().next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "seq expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(SeqSet::new(set).into());
        }
        if tok == MATRIX {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "matrix expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "matrix expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let row_len = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "matrix expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let col_len = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "matrix expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(MatrixSet::new(set, row_len, col_len).into());
        }

        if tok == POWER_SET {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "power_set expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "power_set expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(PowerSet::new(value).into());
        }
        if tok == GENERAL_CART {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "general_cart expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let index_set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "general_cart expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let family_set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "general_cart expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let family_fn = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "general_cart expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(GeneralCart::new(index_set, family_set, family_fn).into());
        }
        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_dim expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_dim expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(CartDim::new(value).into());
        }
        if tok == FINITE_SET_SIZE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_size expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_size expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(FiniteSetSize::new(value).into());
        }
        if tok == FINITE_SET_MAX || tok == FINITE_SET_MIN {
            let is_max = tok == FINITE_SET_MAX;
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                let name = if is_max {
                    FINITE_SET_MAX
                } else {
                    FINITE_SET_MIN
                };
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{name} expects 1 argument"),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite-set extrema expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return if is_max {
                Ok(FiniteSetMax::new(set).into())
            } else {
                Ok(FiniteSetMin::new(set).into())
            };
        }
        if tok == FN_RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "fn_range expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let function = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "fn_range expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(FnRange::new(function).into());
        }
        if tok == REPLACEMENT {
            tb.skip()?;
            return self.parse_replacement_obj(tb);
        }
        if tok == REDUCE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 5 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "reduce expects 5 arguments (start, end, function, operation, seed)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let [start, end, func, op, seed]: [Obj; 5] = args.try_into().map_err(|_| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "reduce expects 5 arguments (start, end, function, operation, seed)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Reduce::new(start, end, func, op, seed).into());
        }
        if tok == FINITE_SET_REDUCE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 4 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_reduce expects 4 arguments (set, function, operation, seed)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let [set, func, op, seed]: [Obj; 4] = args.try_into().map_err(|_| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_reduce expects 4 arguments (set, function, operation, seed)"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(FiniteSetReduce::new(set, func, op, seed).into());
        }
        if tok == SUM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "sum expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let start = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "sum expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let end = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "sum expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let func = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "sum expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Sum::new(start, end, func).into());
        }
        if tok == FINITE_SET_SUM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_sum expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_sum expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let func = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_sum expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(SumOfFiniteSet::new(set, func).into());
        }
        if tok == PRODUCT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "product expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let start = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "product expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let end = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "product expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let func = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "product expects 3 arguments (start, end, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Product::new(start, end, func).into());
        }
        if tok == FINITE_SET_PRODUCT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_product expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_product expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let func = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "finite_set_product expects 2 arguments (set, function)".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(ProductOfFiniteSet::new(set, func).into());
        }
        if tok == CART {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() < 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cart expects at least 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            return Ok(Cart::new(args).into());
        }

        if tok == TUPLE_DIM {
            tb.skip()?;
            let args = self.parse_braced_obj(tb)?;
            return Ok(TupleDim::new(args).into());
        }

        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_obj(tb)?;
            return Ok(CartDim::new(args).into());
        }

        // Bare `ident` or `mod::ident`: built-in single-token `StandardSet` names, else free params.
        self.parse_and_reclassify_atom_as_free_param_obj(tb)
    }

    // parse_identifier_or_identifier_with_mod + reclassify (builtin sets + free params).
    pub(super) fn parse_and_reclassify_atom_as_free_param_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let atom = self.parse_identifier_or_identifier_with_mod(tb)?;
        self.reclassify_atom_as_free_param_obj(atom)
    }

    fn reclassify_atom_as_free_param_obj(&self, obj: Obj) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Atom(AtomObj::Identifier(id)) => {
                if let Some(standard) = standard_set_from_bare_identifier_name(&id.name) {
                    return Ok(standard);
                }
                let is_bound_in_parse_scope = self
                    .current_parse_context()
                    .free_params
                    .name_is_in_any_free_param_map(&id.name);
                let resolved = self
                    .current_parse_context()
                    .free_params
                    .resolve_identifier_to_free_param_obj(&id.name);
                if is_bound_in_parse_scope {
                    return Ok(resolved);
                }
                match resolved {
                    Obj::Atom(AtomObj::Identifier(id)) => {
                        Ok(self.qualify_bare_identifier_if_needed(id))
                    }
                    _ => Ok(resolved),
                }
            }
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => {
                Ok(Obj::Atom(AtomObj::IdentifierWithMod(m)))
            }
            _ => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(
                    "internal: atom position was not a name form".to_string(),
                ),
            ))),
        }
    }
}

// Maps a built-in one-token standard-set symbol to Obj::StandardSet; see reclassify_atom_as_free_param_obj.
fn standard_set_from_bare_identifier_name(name: &str) -> Option<Obj> {
    match name {
        N_POSITIVE | Z_POSITIVE => Some(StandardSet::NPos.into()),
        N => Some(StandardSet::N.into()),
        Q => Some(StandardSet::Q.into()),
        Z => Some(StandardSet::Z.into()),
        R => Some(StandardSet::R.into()),
        C => Some(StandardSet::C.into()),
        Q_POSITIVE => Some(StandardSet::QPos.into()),
        R_POSITIVE => Some(StandardSet::RPos.into()),
        Q_NEGATIVE => Some(StandardSet::QNeg.into()),
        Z_NEGATIVE => Some(StandardSet::ZNeg.into()),
        R_NEGATIVE => Some(StandardSet::RNeg.into()),
        Q_NOT_ZERO => Some(StandardSet::QStar.into()),
        Z_NOT_ZERO => Some(StandardSet::ZStar.into()),
        R_NOT_ZERO => Some(StandardSet::RStar.into()),
        C_NOT_ZERO => Some(StandardSet::CStar.into()),
        _ => None,
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/parse/object/primary/keyword_objects.rs"]
mod keyword_object_tests;
