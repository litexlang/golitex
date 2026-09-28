//! Object-expression precedence, operators, calls, fields, and literals.

use crate::prelude::*;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        self.parse_unicode_union(tb)
    }

    /// Unicode set union has the lowest object-expression precedence.
    fn parse_unicode_union(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_unicode_intersect(tb)?;
        while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(UNICODE_UNION) {
            tb.skip_token(UNICODE_UNION)?;
            let right = self.parse_unicode_intersect(tb)?;
            left = Union::new(left, right).into();
        }
        Ok(left)
    }

    /// Unicode set intersection binds tighter than union.
    fn parse_unicode_intersect(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_unicode_cart(tb)?;
        while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(UNICODE_INTERSECT) {
            tb.skip_token(UNICODE_INTERSECT)?;
            let right = self.parse_unicode_cart(tb)?;
            left = Intersect::new(left, right).into();
        }
        Ok(left)
    }

    /// Unicode Cartesian product binds tighter than set intersection and flattens a direct chain.
    fn parse_unicode_cart(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let first = self.parse_obj_hierarchy1(tb)?;
        if tb.exceed_end_of_head() || !tb.current_token_is_equal_to(UNICODE_CART) {
            return Ok(first);
        }

        let mut factors = vec![first];
        while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(UNICODE_CART) {
            tb.skip_token(UNICODE_CART)?;
            factors.push(self.parse_obj_hierarchy1(tb)?);
        }
        Ok(Cart::new(factors).into())
    }

    /// Lowest-precedence arithmetic operators; left associative, e.g. `2 + 3 - 4`.
    fn parse_obj_hierarchy1(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_obj_hierarchy2(tb)?;
        loop {
            if tb.exceed_end_of_head() {
                return Ok(left);
            }
            if tb.current_token_is_equal_to(ADD) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy2(tb)?;

                left = self.new_parsed_add(left, right)?;
            } else if tb.current_token_is_equal_to(SUB) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy2(tb)?;
                left = self.new_parsed_sub(left, right)?;
            } else {
                return Ok(left);
            }
        }
    }

    /// Multiplicative operators bind tighter than `+` and `-`; left associative.
    fn parse_obj_hierarchy2(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_obj_hierarchy3(tb)?;
        loop {
            if tb.exceed_end_of_head() {
                return Ok(left);
            }
            if tb.current_token_is_equal_to(MUL) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = self.new_parsed_mul(left, right)?;
            } else if tb.current_token_is_equal_to(DIV) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = self.new_parsed_div(left, right)?;
            } else if tb.current_token_is_equal_to(MOD) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = Mod::new(left, right).into();
            } else if tb.current_token_is_equal_to(MATRIX_SCALAR_MUL) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = MatrixScalarMul::new(left, right).into();
            } else {
                return Ok(left);
            }
        }
    }

    /// Closed interval `...` binds tighter than multiplication and accepts signed endpoints.
    fn parse_obj_hierarchy3(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy4(tb)?;

        if tb.current_token_is_equal_to(DOT_DOT_DOT) {
            tb.skip_token(DOT_DOT_DOT)?;
            let right = self.parse_obj_hierarchy1(tb)?;
            Ok(ClosedRange::new(left, right).into())
        } else {
            Ok(left)
        }
    }

    /// Prefix `-` binds below power and postfixes, but above multiplicative operators.
    fn parse_obj_hierarchy4(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        if !tb.current_token_is_equal_to(SUB) {
            return self.parse_obj_hierarchy5(tb);
        }
        if minus_token_is_standalone_operator_obj(tb) {
            tb.skip()?;
            return Ok(Identifier::new_bound(
                SUB.to_string(),
                builtin_symbol_ref(SUB).expect("minus is a builtin symbol"),
            )
            .into());
        }

        tb.skip()?;
        let obj = self.parse_obj_hierarchy4(tb)?;
        self.new_parsed_mul(Number::new("-1".to_string()).into(), obj)
    }

    /// Power and matrix operators bind tighter than prefix `-`; power is right associative.
    fn parse_obj_hierarchy5(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy6(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(POW) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy4(tb)?;
            Ok(Pow::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_POW) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy4(tb)?;
            Ok(MatrixPow::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_MUL) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy4(tb)?;
            Ok(MatrixMul::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_SUB) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy4(tb)?;
            Ok(MatrixSub::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_ADD) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy4(tb)?;
            Ok(MatrixAdd::new(left, right).into())
        } else {
            Ok(left)
        }
    }

    /// Postfix field access, calls, and subscript `[]` bind tighter than `^`.
    fn parse_obj_hierarchy6(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_obj_hierarchy7(tb)?;
        left = self.parse_field_and_call_postfixes(tb, left)?;
        loop {
            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                tb.skip_token(LEFT_BRACKET)?;
                let obj = self.parse_obj(tb)?;
                tb.skip_token(RIGHT_BRACKET)?;
                left = ObjAtIndex::new(left, obj).into();
                left = self.parse_field_and_call_postfixes(tb, left)?;
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Primary: `{ }`, `fn`, numbers, `()`, keywords, atoms.
    fn parse_obj_hierarchy7(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        if tb.current_token_is_equal_to(LEFT_CURLY_BRACE) {
            self.parse_set_builder_or_set_list(tb)
        } else if tb.current_token_is_equal_to(LEFT_BRACKET) {
            tb.skip_token(LEFT_BRACKET)?;
            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                let mut rows: Vec<Vec<Obj>> = vec![];
                loop {
                    tb.skip_token(LEFT_BRACKET)?;
                    let mut row: Vec<Obj> = vec![];
                    if !tb.current_token_is_equal_to(RIGHT_BRACKET) {
                        row.push(self.parse_obj(tb)?);
                        while tb.current_token_is_equal_to(COMMA) {
                            tb.skip_token(COMMA)?;
                            row.push(self.parse_obj(tb)?);
                        }
                    }
                    tb.skip_token(RIGHT_BRACKET)?;
                    rows.push(row);
                    if tb.current_token_is_equal_to(COMMA) {
                        tb.skip_token(COMMA)?;
                        if !tb.current_token_is_equal_to(LEFT_BRACKET) {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file(
                                    "matrix literal: expected `[` after `,` between rows"
                                        .to_string(),
                                    tb.line_file.clone(),
                                ),
                            )));
                        }
                    } else if tb.current_token_is_equal_to(RIGHT_BRACKET) {
                        tb.skip_token(RIGHT_BRACKET)?;
                        return Ok(MatrixListObj::new(rows).into());
                    } else {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "matrix literal: expected `,` or closing `]`".to_string(),
                                tb.line_file.clone(),
                            ),
                        )));
                    }
                }
            } else if tb.current_token_is_equal_to(RIGHT_BRACKET) {
                tb.skip_token(RIGHT_BRACKET)?;
                let list = FiniteSeqListObj::new(vec![]);
                let mut result: Obj = list.clone().into();
                let head = FnObjHead::FiniteSeqListObj(list);
                let mut body_vectors: Vec<Vec<Box<Obj>>> = vec![];
                while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
                    let args = self.parse_fn_obj_arg_group(tb)?;
                    let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
                    body_vectors.push(group);
                }
                if !body_vectors.is_empty() {
                    result = self.new_parsed_fn_obj(head, body_vectors)?;
                }
                Ok(result)
            } else {
                let mut objs = vec![self.parse_obj(tb)?];
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    objs.push(self.parse_obj(tb)?);
                }
                tb.skip_token(RIGHT_BRACKET)?;
                let list = FiniteSeqListObj::new(objs);
                let mut result: Obj = list.clone().into();
                let head = FnObjHead::FiniteSeqListObj(list);
                let mut body_vectors: Vec<Vec<Box<Obj>>> = vec![];
                while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
                    let args = self.parse_fn_obj_arg_group(tb)?;
                    let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
                    body_vectors.push(group);
                }
                if !body_vectors.is_empty() {
                    result = self.new_parsed_fn_obj(head, body_vectors)?;
                }
                Ok(result)
            }
        } else if tb.current_token_is_equal_to(INTERVAL_LITERAL_PREFIX) {
            self.parse_two_sided_interval_literal(tb)
        } else if tb.current_token_is_equal_to(FN_LOWER_CASE) {
            tb.skip_token(FN_LOWER_CASE)?;
            let fn_set = self.parse_fn_set(tb)?;
            let mut result: Obj = if tb.current_token_is_equal_to(LEFT_CURLY_BRACE) {
                let fn_param_bindings = fn_set.get_param_bindings();
                let equal_to = self.parse_in_existing_free_param_scope(
                    BindingScope::LocalBinder,
                    &fn_param_bindings,
                    tb.line_file.clone(),
                    |this| {
                        tb.skip_token(LEFT_CURLY_BRACE)?;
                        let equal_to = this.parse_obj(tb)?;
                        tb.skip_token(RIGHT_CURLY_BRACE)?;
                        Ok(equal_to)
                    },
                )?;
                self.new_anonymous_fn(
                    fn_set.body.set_bound_parameters.clone(),
                    fn_set.body.dom_facts.clone(),
                    (*fn_set.body.ret_set).clone(),
                    equal_to,
                )?
                .into()
            } else {
                fn_set.into()
            };
            if let Obj::AnonymousFn(anon) = &result {
                let mut body_vectors: Vec<Vec<Box<Obj>>> = vec![];
                while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
                    let args = self.parse_fn_obj_arg_group(tb)?;
                    let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
                    body_vectors.push(group);
                }
                if !body_vectors.is_empty() {
                    let head = FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()));
                    result = self.new_parsed_fn_obj(head, body_vectors)?;
                }
            }
            Ok(result)
        } else {
            self.parse_number_or_primary_obj_or_fn_obj(tb)
        }
    }

    pub fn parse_fn_set(&mut self, tb: &mut TokenBlock) -> Result<FnSet, RuntimeError> {
        let fn_set = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(LEFT_BRACE)?;
            let mut set_bound_parameters: Vec<SetBoundParameterGroup> = vec![];
            loop {
                let param = parse_synthetically_correct_identifier_string(tb)?;
                let mut current_params = vec![param];

                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    current_params.push(parse_synthetically_correct_identifier_string(tb)?);
                }

                let param_set = this.parse_obj(tb)?;
                let bindings = this.begin_parsing_scope(
                    BindingScope::LocalBinder,
                    &current_params,
                    tb.line_file.clone(),
                )?;
                set_bound_parameters.push(SetBoundParameterGroup::new(bindings, param_set));

                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    continue;
                } else if tb.current_token_is_equal_to(COLON) {
                    break;
                } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                    break;
                } else {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected comma or colon".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            }

            let all_fn_names = SetBoundParameterGroup::collect_param_names(&set_bound_parameters);

            let mut dom_facts = vec![];
            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                let cur = this.parse_quantifier_free_fact(tb)?;
                dom_facts.push(cur);
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    let cur = this.parse_quantifier_free_fact(tb)?;
                    dom_facts.push(cur);
                }
            }

            tb.skip_token(RIGHT_BRACE)?;
            let ret_set_parsed = this.parse_obj(tb)?;
            this.end_parsing_scope(&all_fn_names);
            let built = this.new_fn_set(set_bound_parameters, dom_facts, ret_set_parsed);
            Ok(FnSetOrFnSetClause::FnSet(built?))
        });
        match fn_set {
            Ok(fn_set) => match fn_set {
                FnSetOrFnSetClause::FnSet(fn_set) => Ok(fn_set),
                FnSetOrFnSetClause::FnSetClause(_) => {
                    panic!("FnSetOrFnSetClause::FnSetClause should not be returned");
                }
            },
            Err(e) => Err(e),
        }
    }

    pub fn parse_fn_set_clause(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<FnSetClause, RuntimeError> {
        let clause = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(LEFT_BRACE)?;
            let mut set_bound_parameters: Vec<SetBoundParameterGroup> = vec![];
            loop {
                let param = parse_synthetically_correct_identifier_string(tb)?;
                let mut current_params = vec![param];

                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    current_params.push(parse_synthetically_correct_identifier_string(tb)?);
                }

                let param_set = this.parse_obj(tb)?;
                let bindings = this.begin_parsing_scope(
                    BindingScope::LocalBinder,
                    &current_params,
                    tb.line_file.clone(),
                )?;
                set_bound_parameters.push(SetBoundParameterGroup::new(bindings, param_set));

                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    continue;
                } else if tb.current_token_is_equal_to(COLON) {
                    break;
                } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                    break;
                } else {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected comma or colon".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            }

            let all_fn_names = SetBoundParameterGroup::collect_param_names(&set_bound_parameters);

            let mut dom_facts = vec![];
            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                let cur = this.parse_quantifier_free_fact(tb)?;
                dom_facts.push(cur);
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    let cur = this.parse_quantifier_free_fact(tb)?;
                    dom_facts.push(cur);
                }
            }

            tb.skip_token(RIGHT_BRACE)?;
            let ret_set_parsed = this.parse_obj(tb)?;
            this.end_parsing_scope(&all_fn_names);
            let clause_ok = FnSetClause::new(set_bound_parameters, dom_facts, ret_set_parsed)?;
            Ok(FnSetOrFnSetClause::FnSetClause(clause_ok))
        });
        match clause {
            Ok(clause) => match clause {
                FnSetOrFnSetClause::FnSetClause(clause) => Ok(clause),
                FnSetOrFnSetClause::FnSet(_) => {
                    panic!("FnSetOrFnSetClause::FnSet should not be returned");
                }
            },
            Err(e) => Err(e),
        }
    }

    /// Parses a numeric literal, primary object, or callable head with argument groups.
    fn parse_number_or_primary_obj_or_fn_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let token = tb.current()?;

        // 0. Parenthesized object or tuple.
        if token == LEFT_BRACE {
            tb.skip()?;
            let obj = self.parse_obj(tb)?;

            if tb.current_token_is_equal_to(COMMA) {
                let mut args = vec![obj];
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;

                    args.push(self.parse_obj(tb)?);
                }
                tb.skip_token(RIGHT_BRACE)?;
                return Ok(Tuple::new(args).into());
            } else {
                tb.skip_token(RIGHT_BRACE)?;
                let Some(head) = FnObjHead::from_callable_obj(obj.clone()) else {
                    return Ok(obj);
                };
                let mut body_vectors = vec![];
                while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
                    let args = self.parse_fn_obj_arg_group(tb)?;
                    body_vectors.push(args.into_iter().map(Box::new).collect());
                }
                if body_vectors.is_empty() {
                    return Ok(obj);
                }
                return self.new_parsed_fn_obj(head, body_vectors);
            }
        }

        // 1. Numeric literal.
        if starts_with_digit(token) {
            let number = tb.advance()?;
            // If the line ends here, validate and return the number directly.
            if tb.exceed_end_of_head() {
                if !is_number(&number) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return Ok(Number::new(number).into());
            }

            if tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let fraction = tb.advance()?;
                let number = format!("{}{}{}", number, DOT_AKA_FIELD_ACCESS_SIGN, fraction);
                if !is_number(&number) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return Ok(Number::new(number).into());
            } else {
                if !is_number(&number) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return Ok(Number::new(number).into());
            }
        }

        // 2. Parse a primary object; builtin standard-set names are reclassified later.
        let result = self.parse_primary_obj(tb)?;

        // 3. Calls and defined-field projections are ordinary composable postfixes.
        self.parse_field_and_call_postfixes(tb, result)
    }

    fn parse_field_and_call_postfixes(
        &mut self,
        tb: &mut TokenBlock,
        mut result: Obj,
    ) -> Result<Obj, RuntimeError> {
        loop {
            if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(DOT_AKA_FIELD_ACCESS_SIGN) {
                tb.skip_token(DOT_AKA_FIELD_ACCESS_SIGN)?;
                let field_name = parse_struct_field_name(tb)?;
                result = ObjAsStructInstanceWithFieldAccess::new(result, field_name).into();
                continue;
            }

            if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
                let Some(head) = FnObjHead::from_callable_obj(result.clone()) else {
                    return Ok(result);
                };
                let mut body_vectors = Vec::new();
                while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
                    let args = self.parse_fn_obj_arg_group(tb)?;
                    body_vectors.push(args.into_iter().map(Box::new).collect());
                }
                result = self.new_parsed_fn_obj(head, body_vectors)?;
                continue;
            }

            return Ok(result);
        }
    }
}

fn starts_with_digit(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false)
}

fn minus_token_is_standalone_operator_obj(tb: &TokenBlock) -> bool {
    let next = tb.token_at_add_index(1);
    next == FACT_PREFIX
        || next == EQUAL
        || next == NOT_EQUAL
        || next == LESS
        || next == GREATER
        || next == LESS_EQUAL
        || next == GREATER_EQUAL
}

fn is_number(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let mut dot_count = 0;

    for c in s.chars() {
        if c == '.' {
            dot_count += 1;
            if dot_count > 1 {
                return false;
            }
        } else if !c.is_ascii_digit() {
            return false;
        }
    }

    s != "."
}

enum FnSetOrFnSetClause {
    FnSet(FnSet),
    FnSetClause(FnSetClause),
}

pub(super) fn parse_synthetically_correct_identifier_string(
    tb: &mut TokenBlock,
) -> Result<String, RuntimeError> {
    let cur = tb.advance()?;

    if cur == SET || cur == NONEMPTY_SET || cur == FINITE_SET {
        return Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                format!("{} is not a valid identifier", cur),
                tb.line_file.clone(),
            ),
        )));
    }

    Ok(cur)
}

fn parse_struct_field_name(tb: &mut TokenBlock) -> Result<String, RuntimeError> {
    let field_name = parse_synthetically_correct_identifier_string(tb)?;
    validate_litex_name_for_parse(&field_name, tb.line_file.clone())?;
    Ok(field_name)
}

pub(super) fn validate_litex_name_for_parse(
    name: &str,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    is_valid_litex_name(name).map_err(|msg| {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file),
        ))
    })
}

pub(super) fn validate_module_path_segment_for_parse(
    name: &str,
    is_root_segment: bool,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    if is_root_segment && name == STD {
        return Ok(());
    }
    validate_litex_name_for_parse(name, line_file)
}

#[cfg(test)]
#[path = "../../../tests/unit/parsing/object/expression/module_qualification.rs"]
mod module_qualification_tests;

#[cfg(test)]
#[path = "../../../tests/unit/parsing/object/expression/precedence.rs"]
mod precedence_tests;
