use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        self.parse_obj_hierarchy1(tb)
    }

    /// Lowest-precedence additive operators; left associative, e.g. `2 + 3 - 4`.
    fn parse_obj_hierarchy1(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_obj_hierarchy2(tb)?;
        loop {
            if tb.exceed_end_of_head() {
                return Ok(left);
            }
            if tb.current_token_is_equal_to(ADD) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy2(tb)?;

                left = Add::new(left, right).into();
            } else if tb.current_token_is_equal_to(SUB) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy2(tb)?;
                left = Sub::new(left, right).into();
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
                left = Mul::new(left, right).into();
            } else if tb.current_token_is_equal_to(DIV) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = Div::new(left, right).into();
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

    /// Power and matrix operators bind tighter than multiplication; power is right associative.
    fn parse_obj_hierarchy3(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy4(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(POW) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?; // Right associative: the right side may contain another `^`.
            Ok(Pow::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_POW) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?;
            Ok(MatrixPow::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_MUL) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?;
            Ok(MatrixMul::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_SUB) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?;
            Ok(MatrixSub::new(left, right).into())
        } else if tb.current_token_is_equal_to(MATRIX_ADD) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?;
            Ok(MatrixAdd::new(left, right).into())
        } else {
            Ok(left)
        }
    }

    /// Subscript `[]`, tighter than `^`.
    fn parse_obj_hierarchy4(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut left = self.parse_obj_hierarchy5(tb)?;
        loop {
            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                tb.skip_token(LEFT_BRACKET)?;
                let obj = self.parse_obj(tb)?;
                tb.skip_token(RIGHT_BRACKET)?;
                left = ObjAtIndex::new(left, obj).into();
            } else {
                break;
            }
        }
        if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
            let head = match &left {
                Obj::ObjAtIndex(x) => FnObjHead::ObjAtIndex(x.clone()),
                Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                    FnObjHead::ObjAsStructInstanceWithFieldAccess(x.clone())
                }
                _ => return Ok(left),
            };
            let mut body_vectors = vec![];
            while !tb.exceed_end_of_head() && tb.current_token_is_equal_to(LEFT_BRACE) {
                let args = self.parse_fn_obj_arg_group(tb)?;
                let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
                body_vectors.push(group);
            }
            left = FnObj::new(head, body_vectors).into();
        }
        Ok(left)
    }

    /// Infix closed interval `...` (`closed_range`); same band as `[]`, applied after subscripts.
    fn parse_obj_hierarchy5(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy6(tb)?;

        if tb.current_token_is_equal_to(DOT_DOT_DOT) {
            tb.skip_token(DOT_DOT_DOT)?;
            let right = self.parse_obj_hierarchy1(tb)?;
            Ok(ClosedRange::new(left, right).into())
        } else {
            Ok(left)
        }
    }

    /// Primary: `{ }`, `fn`, numbers, `()`, keywords, atoms.
    fn parse_obj_hierarchy6(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
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
                    result = FnObj::new(head, body_vectors).into();
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
                    result = FnObj::new(head, body_vectors).into();
                }
                Ok(result)
            }
        } else if tb.current_token_is_equal_to(INTERVAL_LITERAL_PREFIX) {
            self.parse_two_sided_interval_literal(tb)
        } else if tb.current_token_is_equal_to(FN_LOWER_CASE) {
            tb.skip_token(FN_LOWER_CASE)?;
            let fn_set = self.parse_fn_set(tb)?;
            let mut result: Obj = if tb.current_token_is_equal_to(LEFT_CURLY_BRACE) {
                let all_fn_names =
                    ParamGroupWithSet::collect_param_names(&fn_set.body.params_def_with_set);
                let equal_to = self.parse_in_local_free_param_scope(
                    ParamObjType::FnSet,
                    &all_fn_names,
                    tb.line_file.clone(),
                    |this| {
                        tb.skip_token(LEFT_CURLY_BRACE)?;
                        let equal_to = this.parse_obj(tb)?;
                        tb.skip_token(RIGHT_CURLY_BRACE)?;
                        Ok(equal_to)
                    },
                )?;
                self.new_anonymous_fn(
                    fn_set.body.params_def_with_set.clone(),
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
                    result = FnObj::new(head, body_vectors).into();
                }
            }
            Ok(result)
        } else {
            self.parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(tb)
        }
    }

    pub fn parse_fn_set(&mut self, tb: &mut TokenBlock) -> Result<FnSet, RuntimeError> {
        let fn_set = self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(LEFT_BRACE)?;
            let mut params_def_with_set: Vec<ParamGroupWithSet> = vec![];
            loop {
                let param = parse_synthetically_correct_identifier_string(tb)?;
                let mut current_params = vec![param];

                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    current_params.push(parse_synthetically_correct_identifier_string(tb)?);
                }

                let param_group = ParamGroupWithSet::new(current_params, this.parse_obj(tb)?);
                this.parsing_free_param_collection.begin_scope(
                    ParamObjType::FnSet,
                    &param_group.params,
                    tb.line_file.clone(),
                )?;

                params_def_with_set.push(param_group);

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

            let all_fn_names = ParamGroupWithSet::collect_param_names(&params_def_with_set);

            let mut dom_facts = vec![];
            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                let cur = this.parse_or_and_chain_atomic_fact(tb)?;
                dom_facts.push(cur);
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    let cur = this.parse_or_and_chain_atomic_fact(tb)?;
                    dom_facts.push(cur);
                }
            }

            tb.skip_token(RIGHT_BRACE)?;
            // Return sets are non-dependent; parse them outside the function-parameter scope.
            this.parsing_free_param_collection
                .end_scope(ParamObjType::FnSet, &all_fn_names);
            let ret_set_parsed = this.parse_obj(tb)?;
            let built = this.new_fn_set(params_def_with_set, dom_facts, ret_set_parsed);
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
            let mut params_def_with_set: Vec<ParamGroupWithSet> = vec![];
            loop {
                let param = parse_synthetically_correct_identifier_string(tb)?;
                let mut current_params = vec![param];

                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    current_params.push(parse_synthetically_correct_identifier_string(tb)?);
                }

                let param_group = ParamGroupWithSet::new(current_params, this.parse_obj(tb)?);
                this.parsing_free_param_collection.begin_scope(
                    ParamObjType::FnSet,
                    &param_group.params,
                    tb.line_file.clone(),
                )?;

                params_def_with_set.push(param_group);

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

            let all_fn_names = ParamGroupWithSet::collect_param_names(&params_def_with_set);

            let mut dom_facts = vec![];
            if tb.current_token_is_equal_to(COLON) {
                tb.skip_token(COLON)?;
                let cur = this.parse_or_and_chain_atomic_fact(tb)?;
                dom_facts.push(cur);
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    let cur = this.parse_or_and_chain_atomic_fact(tb)?;
                    dom_facts.push(cur);
                }
            }

            tb.skip_token(RIGHT_BRACE)?;
            // Return sets are non-dependent; parse them outside the function-parameter scope.
            this.parsing_free_param_collection
                .end_scope(ParamObjType::FnSet, &all_fn_names);
            let ret_set_parsed = this.parse_obj(tb)?;
            let clause_ok = FnSetClause::new(params_def_with_set, dom_facts, ret_set_parsed)?;
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

    pub fn parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        if tb.current_token_is_equal_to(SUB) {
            if minus_token_is_standalone_operator_obj(tb) {
                tb.skip()?;
                return Ok(Identifier::new(SUB.to_string()).into());
            }
            tb.skip()?;
            let obj = self.parse_number_or_primary_obj_or_fn_obj(tb)?;
            Ok(Mul::new(Number::new("-1".to_string()).into(), obj).into())
        } else {
            self.parse_number_or_primary_obj_or_fn_obj(tb)
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
                return Ok(obj);
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
        let mut result = self.parse_primary_obj(tb)?;

        // 3. If the result is callable, parse all following argument groups.
        let (head, mut body_vectors) = match &result {
            Obj::Atom(AtomObj::Identifier(i)) => (FnObjHead::Identifier(i.clone()), vec![]),
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => {
                (FnObjHead::IdentifierWithMod(m.clone()), vec![])
            }
            Obj::Atom(AtomObj::Forall(p)) => (FnObjHead::Forall(p.clone()), vec![]),
            Obj::Atom(AtomObj::Exist(p)) => (FnObjHead::Exist(p.clone()), vec![]),
            Obj::Atom(AtomObj::Def(p)) => (FnObjHead::DefHeader(p.clone()), vec![]),
            Obj::Atom(AtomObj::SetBuilder(p)) => (FnObjHead::SetBuilder(p.clone()), vec![]),
            Obj::Atom(AtomObj::FnSet(p)) => (FnObjHead::FnSet(p.clone()), vec![]),
            Obj::Atom(AtomObj::Induc(p)) => (FnObjHead::Induc(p.clone()), vec![]),
            Obj::Atom(AtomObj::DefAlgo(p)) => (FnObjHead::DefAlgo(p.clone()), vec![]),
            Obj::Atom(AtomObj::DefStructField(p)) => (FnObjHead::DefStructField(p.clone()), vec![]),
            Obj::AnonymousFn(anon) => (
                FnObjHead::AnonymousFnLiteral(Box::new(anon.clone())),
                vec![],
            ),
            Obj::FiniteSeqListObj(list) => (FnObjHead::FiniteSeqListObj(list.clone()), vec![]),
            Obj::ObjAtIndex(x) => (FnObjHead::ObjAtIndex(x.clone()), vec![]),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => (
                FnObjHead::ObjAsStructInstanceWithFieldAccess(x.clone()),
                vec![],
            ),
            Obj::InstantiatedTemplateObj(t) => {
                (FnObjHead::InstantiatedTemplateObj(t.clone()), vec![])
            }
            _ => return Ok(result),
        };
        while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
            let args = self.parse_fn_obj_arg_group(tb)?;
            let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
            body_vectors.push(group);
        }
        if !body_vectors.is_empty() {
            result = FnObj::new(head, body_vectors).into();
        }
        Ok(result)
    }

    /// Parses a primary object from a keyword form or ordinary atom.
    fn parse_primary_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let tok = tb.current()?;

        if tok == STRUCT_VIEW_PREFIX {
            return self.parse_struct_view_obj(tb);
        }
        if tok == TEMPLATE_INSTANCE_PREFIX {
            return self.parse_instantiated_template_obj(tb);
        }
        if tok == ABS {
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(Abs::new(arg).into());
        }
        if tok == SQRT {
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(Sqrt::new(arg).into());
        }
        if tok == INTEGER_QUOTIENT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "integer_quotient expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let dividend = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "integer_quotient expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let divisor = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "integer_quotient expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(IntegerQuotient::new(dividend, divisor).into());
        }
        if tok == MAX {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "max expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "max expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "max expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Max::new(left, right).into());
        }
        if tok == MIN {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "min expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "min expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "min expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Min::new(left, right).into());
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
        if tok == SET_DIFF {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_diff expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_diff expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "set_diff expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(SetDiff::new(left, right).into());
        }
        if tok == CAP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cap expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cap expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Cap::new(value).into());
        }
        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Cup::new(value).into());
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

        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Cup::new(value).into());
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
    fn parse_and_reclassify_atom_as_free_param_obj(
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
                    .parsing_free_param_collection
                    .name_is_in_any_free_param_map(&id.name);
                let resolved = self
                    .parsing_free_param_collection
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

    pub fn parse_braced_objs(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(vec![]);
        }
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    fn parse_two_sided_interval_literal(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(INTERVAL_LITERAL_PREFIX)?;
        let left_closed = match tb.current()? {
            LEFT_BRACE => false,
            LEFT_BRACKET => true,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal after `'` expects `(` or `[`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        tb.skip()?;
        if tb.current_token_is_equal_to(COMMA) {
            if left_closed {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "left-unbounded interval must start with `(`; use `'(,a)` or `'(,a]`"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token(COMMA)?;
            if tb.current_token_is_equal_to(RIGHT_BRACE) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal cannot omit both endpoints; use `R`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let right = self.parse_obj(tb)?;
            if tb.current_token_is_equal_to(COMMA) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal expects exactly two endpoints".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let right_closed = match tb.current()? {
                RIGHT_BRACE => false,
                RIGHT_BRACKET => true,
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "interval literal expects `)` or `]` after its right endpoint"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };
            tb.skip()?;
            return Ok(if right_closed {
                OneSideInfinityIntervalObj::new_right_closed(right).into()
            } else {
                OneSideInfinityIntervalObj::new_right_open(right).into()
            });
        }

        let left = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(if left_closed {
                OneSideInfinityIntervalObj::new_left_closed(left).into()
            } else {
                OneSideInfinityIntervalObj::new_left_open(left).into()
            });
        }
        if tb.current_token_is_equal_to(RIGHT_BRACKET) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "right-unbounded interval must end with `)`; use `'(a,)` or `'[a,)`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let right = self.parse_obj(tb)?;
        if tb.current_token_is_equal_to(COMMA) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "interval literal expects exactly two endpoints".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let right_closed = match tb.current()? {
            RIGHT_BRACE => false,
            RIGHT_BRACKET => true,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal expects `)` or `]` after its right endpoint".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        tb.skip()?;

        Ok(match (left_closed, right_closed) {
            (false, false) => IntervalObj::new_left_open_right_open(left, right).into(),
            (false, true) => IntervalObj::new_left_open_right_closed(left, right).into(),
            (true, false) => IntervalObj::new_left_closed_right_open(left, right).into(),
            (true, true) => IntervalObj::new_left_closed_right_closed(left, right).into(),
        })
    }

    fn parse_angle_bracketed_objs(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LESS)?;
        if tb.current_token_is_equal_to(GREATER) {
            tb.skip_token(GREATER)?;
            return Ok(vec![]);
        }
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(GREATER)?;
        Ok(objs)
    }

    fn parse_fn_obj_arg_group(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        let args = self.parse_braced_objs(tb)?;
        if args.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "function application expects at least one argument".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(args)
    }

    pub fn parse_braced_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parsed_args = self.parse_braced_objs(tb)?;
        if parsed_args.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "expected exactly 1 argument".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let parsed_obj = parsed_args.remove(0);
        Ok(parsed_obj)
    }

    fn parse_replacement_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "replacement expects 2 arguments (prop name, source set)".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let prop_name = self.parse_valid_replacement_prop_name(tb)?;
        tb.skip_token(COMMA)?;
        let source_set = self.parse_obj(tb)?;
        tb.skip_token(RIGHT_BRACE)?;
        Ok(Replacement::new(prop_name, source_set).into())
    }

    fn parse_valid_replacement_prop_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AtomicName, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip()?;
                let part = tb.advance()?;
                parts.push(part);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            for (index, part) in parts.iter().enumerate() {
                validate_module_path_segment_for_parse(part, index == 0, tb.line_file.clone())
                    .map_err(|e| {
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                            None,
                            "replacement expects its first argument to be a prop name".to_string(),
                            tb.line_file.clone(),
                            Some(e),
                            vec![],
                        )))
                    })?;
            }
            validate_litex_name_for_parse(&right, tb.line_file.clone()).map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "replacement expects its first argument to be a prop name".to_string(),
                    tb.line_file.clone(),
                    Some(e),
                    vec![],
                )))
            })?;
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            validate_litex_name_for_parse(&left, tb.line_file.clone()).map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "replacement expects its first argument to be a prop name".to_string(),
                    tb.line_file.clone(),
                    Some(e),
                    vec![],
                )))
            })?;
            Ok(self.qualify_bare_atomic_name_if_needed(left))
        }
    }

    /// Parses a comma-separated object list until the next token is not a comma.
    pub fn parse_obj_list(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        Ok(objs)
    }

    fn parse_set_builder_or_set_list(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(LEFT_CURLY_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_CURLY_BRACE) {
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            return Ok(ListSet::new(vec![]).into());
        }

        let left = self.parse_obj(tb)?;
        // Plain identifiers and parsing-time free-param atoms (e.g. forall-bound `x`) must both
        // allow `{ x S : ... }` set-builder syntax; only `Identifier` was handled originally.
        let name_for_set_builder = match &left {
            Obj::Atom(AtomObj::Identifier(a)) => Some(a.name.as_str()),
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => Some(m.name.as_str()),
            Obj::Atom(AtomObj::Forall(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Def(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Exist(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::FnSet(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Induc(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name.as_str()),
            _ => None,
        };
        if let Some(name) = name_for_set_builder {
            if tb.current_token_is_equal_to(COMMA) || tb.current()? == RIGHT_CURLY_BRACE {
                self.parse_list_set_obj_with_leftmost_obj(tb, left)
            } else {
                self.parse_set_builder(tb, Identifier::new(name.to_string()))
            }
        } else {
            self.parse_list_set_obj_with_leftmost_obj(tb, left)
        }
    }

    fn parse_instantiated_template_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(TEMPLATE_INSTANCE_PREFIX)?;
        let template_name = self.parse_module_qualified_reference_name(tb)?;
        let (left_token, right_token) = if tb.current_token_is_equal_to(LESS) {
            (LESS, GREATER)
        } else {
            (LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE)
        };
        tb.skip_token(left_token)?;
        let mut args = Vec::new();
        if !tb.current_token_is_equal_to(right_token) {
            args.push(self.parse_obj(tb)?);
            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                args.push(self.parse_obj(tb)?);
            }
        }
        tb.skip_token(right_token)?;
        Ok(InstantiatedTemplateObj::new(template_name, args).into())
    }

    /// Parse set builder or list set after the first identifier; wraps body in a name block for the bound variable.
    fn parse_set_builder(
        &mut self,
        tb: &mut TokenBlock,
        a: Identifier,
    ) -> Result<Obj, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| {
            let set_builder_param = [a.name.clone()];
            this.parsing_free_param_collection.begin_scope(
                ParamObjType::SetBuilder,
                &set_builder_param,
                tb.line_file.clone(),
            )?;
            let parsed = (|| -> Result<Obj, RuntimeError> {
                let second = this.parse_obj(tb)?;
                if tb.current()? == COLON {
                    tb.skip_token(COLON)?;

                    let user_names = vec![a.name.clone()];
                    this.validate_user_fn_param_names_for_parse(&user_names, tb.line_file.clone())?;
                    let empty: HashMap<String, Obj> = HashMap::new();
                    let second_inst = this.inst_obj(&second, &empty, ParamObjType::SetBuilder)?;

                    let mut facts_inst = Vec::new();
                    while tb.current()? != RIGHT_CURLY_BRACE {
                        let f = this.parse_exist_body_fact(tb)?;
                        facts_inst.push(this.inst_exist_body_fact(
                            &f,
                            &empty,
                            ParamObjType::SetBuilder,
                            None,
                        )?);
                    }
                    tb.skip_token(RIGHT_CURLY_BRACE)?;

                    Ok(SetBuilder::new(a.name.clone(), second_inst, facts_inst)?.into())
                } else {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "expected colon after first argument".to_string(),
                            tb.line_file.clone(),
                        ),
                    )))
                }
            })();
            this.parsing_free_param_collection
                .end_scope(ParamObjType::SetBuilder, &set_builder_param);
            parsed
        })
    }

    /// Parses a list set after the first object, accepting optional commas between items.
    fn parse_list_set_obj_with_leftmost_obj(
        &mut self,
        tb: &mut TokenBlock,
        left_most_obj: Obj,
    ) -> Result<Obj, RuntimeError> {
        let mut objs = vec![left_most_obj];
        while tb.current()? != RIGHT_CURLY_BRACE {
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(ListSet::new(objs).into())
    }

    pub fn parse_list_set_obj(&mut self, tb: &mut TokenBlock) -> Result<ListSet, RuntimeError> {
        let mut objs = vec![];
        tb.skip_token(LEFT_CURLY_BRACE)?;
        while tb.current()? != RIGHT_CURLY_BRACE {
            objs.push(self.parse_obj(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(ListSet::new(objs))
    }

    pub fn parse_identifier(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        Ok(Identifier::new(left).into())
    }

    fn parse_mod_qualified_atom(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parts = vec![parse_synthetically_correct_identifier_string(tb)?];
        while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip_token(MOD_SIGN)?;
            parts.push(parse_synthetically_correct_identifier_string(tb)?);
        }
        let right = parts
            .pop()
            .expect("qualified name should have a local name");
        let left = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
        if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected `.` after module-qualified name".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(IdentifierWithMod::new(left, right).into())
    }

    /// Unqualified or `::`-qualified name / field name; returns a name-shaped [`Obj`].
    pub fn parse_identifier_or_identifier_with_mod(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let next_is_mod = tb.token_at_add_index(1) == MOD_SIGN;
        if next_is_mod {
            self.parse_mod_qualified_atom(tb)
        } else {
            self.parse_identifier(tb)
        }
    }

    pub fn parse_predicate(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        self.parse_atomic_name(tb)
    }

    pub fn parse_struct_view_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(STRUCT_VIEW_PREFIX)?;
        let name = self.parse_module_qualified_reference_name(tb)?;
        let params = if !tb.exceed_end_of_head() && tb.current()? == LESS {
            self.parse_angle_bracketed_objs(tb)?
        } else if !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
            self.parse_braced_objs(tb)?
        } else {
            vec![]
        };
        let struct_obj = StructObj::new(name, params);

        if tb.exceed_end_of_head() || tb.current()? != LEFT_CURLY_BRACE {
            return Ok(struct_obj.into());
        }

        tb.skip_token(LEFT_CURLY_BRACE)?;
        let obj = self.parse_obj(tb)?;
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        tb.skip_token(DOT_AKA_FIELD_ACCESS_SIGN)?;
        let field_name = parse_synthetically_correct_identifier_string(tb)?;
        Ok(ObjAsStructInstanceWithFieldAccess::new(struct_obj, obj, field_name).into())
    }

    /// `ident` or `mod::ident` as a predicate/atomic name in parse position.
    pub fn parse_atomic_name(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip()?;
                parts.push(parse_synthetically_correct_identifier_string(tb)?);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            Ok(self.qualify_bare_atomic_name_if_needed(left))
        }
    }

    pub(crate) fn parse_module_qualified_reference_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AtomicName, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip_token(MOD_SIGN)?;
                let part = tb.advance()?;
                parts.push(part);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            for (index, part) in parts.iter().enumerate() {
                validate_module_path_segment_for_parse(part, index == 0, tb.line_file.clone())?;
            }
            validate_litex_name_for_parse(&right, tb.line_file.clone())?;
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else if let Some(module_name) = self.current_parse_module_name() {
            validate_litex_name_for_parse(&left, tb.line_file.clone())?;
            Ok(AtomicName::WithMod(module_name, left))
        } else {
            validate_litex_name_for_parse(&left, tb.line_file.clone())?;
            Ok(AtomicName::WithoutMod(left))
        }
    }

    fn current_parse_module_name(&self) -> Option<String> {
        self.current_parse_namespace().map(str::to_string)
    }

    fn qualify_bare_identifier_if_needed(&self, id: Identifier) -> Obj {
        if is_builtin_identifier_name(&id.name) {
            return id.into();
        }
        let Some(module_name) = self.current_parse_module_name() else {
            return id.into();
        };
        IdentifierWithMod::new(module_name, id.name).into()
    }

    fn qualify_bare_atomic_name_if_needed(&self, name: String) -> AtomicName {
        if is_builtin_predicate(&name) {
            return AtomicName::WithoutMod(name);
        }
        let Some(module_name) = self.current_parse_module_name() else {
            return AtomicName::WithoutMod(name);
        };
        AtomicName::WithMod(module_name, name)
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

fn parse_synthetically_correct_identifier_string(
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

fn validate_litex_name_for_parse(name: &str, line_file: LineFile) -> Result<(), RuntimeError> {
    is_valid_litex_name(name).map_err(|msg| {
        RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file),
        ))
    })
}

fn validate_module_path_segment_for_parse(
    name: &str,
    is_root_segment: bool,
    line_file: LineFile,
) -> Result<(), RuntimeError> {
    if is_root_segment && name == STD {
        return Ok(());
    }
    validate_litex_name_for_parse(name, line_file)
}

// Maps a built-in one-token standard-set symbol to Obj::StandardSet; see reclassify_atom_as_free_param_obj.
fn standard_set_from_bare_identifier_name(name: &str) -> Option<Obj> {
    match name {
        N_POS => Some(StandardSet::NPos.into()),
        N => Some(StandardSet::N.into()),
        Q => Some(StandardSet::Q.into()),
        Z => Some(StandardSet::Z.into()),
        R => Some(StandardSet::R.into()),
        Q_POS => Some(StandardSet::QPos.into()),
        R_POS => Some(StandardSet::RPos.into()),
        Q_NEG => Some(StandardSet::QNeg.into()),
        Z_NEG => Some(StandardSet::ZNeg.into()),
        R_NEG => Some(StandardSet::RNeg.into()),
        Q_NZ => Some(StandardSet::QNz.into()),
        Z_NZ => Some(StandardSet::ZNz.into()),
        R_NZ => Some(StandardSet::RNz.into()),
        _ => None,
    }
}

#[cfg(test)]
mod module_qualification_parse_tests {
    use crate::parse::Tokenizer;
    use crate::prelude::*;
    use std::rc::Rc;

    fn parse_one_obj_line_with_runtime(rt: &mut Runtime, line: &str) -> Obj {
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(line, Rc::from("test.lit"))
            .expect("tokenize object line");
        assert_eq!(blocks.len(), 1, "{line:?}");
        rt.parse_obj(&mut blocks[0]).expect("parse object line")
    }

    fn parse_one_fact_line_with_runtime(rt: &mut Runtime, line: &str) -> Fact {
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(line, Rc::from("test.lit"))
            .expect("tokenize fact line");
        assert_eq!(blocks.len(), 1, "{line:?}");
        rt.parse_fact(&mut blocks[0]).expect("parse fact line")
    }

    fn parse_one_stmt_line_with_runtime(rt: &mut Runtime, line: &str) -> Stmt {
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(line, Rc::from("test.lit"))
            .expect("tokenize stmt line");
        assert_eq!(blocks.len(), 1, "{line:?}");
        rt.parse_stmt(&mut blocks[0]).expect("parse stmt line")
    }

    fn set_test_module_name(rt: &mut Runtime, module_name: &str) {
        if rt.execution_stack.is_empty() {
            rt.new_file_path_new_env_new_name_scope("test.lit");
        }
        rt.current_module_mut().module_name = module_name.to_string();
    }

    fn assert_with_mod(name: &AtomicName, expected_mod_name: &str, expected_name: &str) {
        let AtomicName::WithMod(mod_name, name) = name else {
            panic!("expected module-qualified name");
        };
        assert_eq!(mod_name, expected_mod_name);
        assert_eq!(name, expected_name);
    }

    fn assert_without_mod(name: &AtomicName, expected_name: &str) {
        let AtomicName::WithoutMod(name) = name else {
            panic!("expected bare name");
        };
        assert_eq!(name, expected_name);
    }

    #[test]
    fn parses_angle_bracketed_struct_params_and_field_access() {
        let mut rt = Runtime::new();

        let stmt = parse_one_stmt_line_with_runtime(
            &mut rt,
            "struct Group<s set>:\n    inv fn(x s) s\n    op fn(x, y s) s\n    e s",
        );
        let Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(stmt)) = stmt else {
            panic!("expected struct definition");
        };
        let Some((param_def, _)) = &stmt.param_def_with_dom else {
            panic!("expected struct parameter definition");
        };
        assert_eq!(param_def.collect_param_names(), vec!["s".to_string()]);
        assert_eq!(format!("{}", stmt), "struct Group<s set>:");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "&Group<s>{p}.op");
        let Obj::ObjAsStructInstanceWithFieldAccess(access) = obj else {
            panic!("expected struct field access");
        };
        assert_without_mod(&access.struct_obj.name, "Group");
        assert_eq!(access.struct_obj.params.len(), 1);
        assert_eq!(access.field_name, "op");
        assert_eq!(format!("{}", access), "&Group<s>{p}.op");

        let old_obj = parse_one_obj_line_with_runtime(&mut rt, "&Group(s){p}.op");
        assert_eq!(format!("{}", old_obj), "&Group<s>{p}.op");

        let projected_call = parse_one_obj_line_with_runtime(&mut rt, "p[2](x, y)");
        assert_eq!(format!("{}", projected_call), "p[2](x, y)");

        let field_call = parse_one_obj_line_with_runtime(&mut rt, "&Group<s>{p}.op(x, y)");
        assert_eq!(format!("{}", field_call), "&Group<s>{p}.op(x, y)");
    }

    #[test]
    fn module_qualification_keeps_definition_name_bare() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let stmt = parse_one_stmt_line_with_runtime(&mut rt, "abstract_prop some_prop(x)");

        let Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(stmt)) = stmt else {
            panic!("expected abstract prop definition");
        };
        assert_eq!(stmt.name, "some_prop");
    }

    #[test]
    fn parses_replacement_object_prop_name_arguments() {
        let mut rt = Runtime::new();

        let obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(P, A)");
        let Obj::Replacement(replacement) = obj else {
            panic!("expected replacement object");
        };
        assert_without_mod(&replacement.prop_name, "P");
        assert_eq!(format!("{}", replacement), "replacement(P, A)");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(M::P, A)");
        let Obj::Replacement(replacement) = obj else {
            panic!("expected replacement object");
        };
        assert_with_mod(&replacement.prop_name, "M", "P");
        assert_eq!(format!("{}", replacement), "replacement(M::P, A)");
    }

    #[test]
    fn replacement_rejects_non_name_first_argument() {
        let mut rt = Runtime::new();
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("replacement(1, A)", Rc::from("test.lit"))
            .expect("tokenize object line");
        assert_eq!(blocks.len(), 1);
        let err = match rt.parse_obj(&mut blocks[0]) {
            Ok(obj) => panic!("replacement should reject numbers, parsed {}", obj),
            Err(err) => err,
        };
        let RuntimeError::ParseError(err) = err else {
            panic!("expected parse error");
        };
        assert!(
            err.msg
                .contains("replacement expects its first argument to be a prop name"),
            "unexpected error: {}",
            err.msg
        );
    }

    #[test]
    fn module_qualification_qualifies_bare_predicate_but_not_bound_arg() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let fact = parse_one_fact_line_with_runtime(&mut rt, "forall x Z:\n    $some_prop(x)");

        let Fact::ForallFact(forall_fact) = fact else {
            panic!("expected forall fact");
        };
        assert_eq!(forall_fact.then_facts.len(), 1);
        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(atomic_fact)) =
            &forall_fact.then_facts[0]
        else {
            panic!("expected normal atomic fact");
        };
        let AtomicName::WithMod(mod_name, name) = &atomic_fact.predicate else {
            panic!("expected module-qualified predicate");
        };
        assert_eq!(mod_name, "Nat");
        assert_eq!(name, "some_prop");
        let Obj::Atom(AtomObj::Forall(arg)) = &atomic_fact.body[0] else {
            panic!("expected forall-bound argument");
        };
        assert_eq!(arg.name, "x");
    }

    #[test]
    fn module_qualification_qualifies_bare_identifier() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "a");

        let Obj::Atom(AtomObj::IdentifierWithMod(id)) = obj else {
            panic!("expected module-qualified identifier");
        };
        assert_eq!(id.mod_name, "Nat");
        assert_eq!(id.name, "a");
    }

    #[test]
    fn backtick_infix_function_syntax_is_rejected() {
        let mut rt = Runtime::new();
        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("a ` f b = c", Rc::from("test.lit"))
            .expect("tokenize stmt line");
        assert_eq!(blocks.len(), 1);
        assert!(rt.parse_stmt(&mut blocks[0]).is_err());
    }

    #[test]
    fn module_qualification_qualifies_source_identifier() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "pi");

        let Obj::Atom(AtomObj::IdentifierWithMod(id)) = obj else {
            panic!("expected module-qualified source identifier");
        };
        assert_eq!(id.mod_name, "Nat");
        assert_eq!(id.name, "pi");
    }

    #[test]
    fn module_qualification_keeps_finite_set_size_builtin_bare() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "finite_set_size({1, 2})");

        let Obj::FiniteSetSize(_) = obj else {
            panic!("expected finite_set_size builtin object");
        };
    }

    #[test]
    fn module_qualification_qualifies_bare_thm_strategy_template_and_struct_refs() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by thm T(a)");
        let Stmt::By(ByStmt::ByThmStmt(thm_stmt)) = thm_stmt else {
            panic!("expected by thm stmt");
        };
        assert_with_mod(&thm_stmt.name, "Nat", "T");

        let strategy_stmt = parse_one_stmt_line_with_runtime(&mut rt, "use strategy S");
        let Stmt::Command(CommandStmt::UseStrategyStmt(strategy_stmt)) = strategy_stmt else {
            panic!("expected use strategy stmt");
        };
        assert_with_mod(&strategy_stmt.name, "Nat", "S");

        let stop_stmt = parse_one_stmt_line_with_runtime(&mut rt, "stop strategy S");
        let Stmt::Command(CommandStmt::StopStrategyStmt(stop_stmt)) = stop_stmt else {
            panic!("expected stop strategy stmt");
        };
        assert_with_mod(&stop_stmt.name, "Nat", "S");

        let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Template<2>");
        let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
            panic!("expected instantiated template object");
        };
        assert_with_mod(&template_obj.template_name, "Nat", "Template");

        let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Struct");
        let Obj::StructObj(struct_obj) = struct_obj else {
            panic!("expected struct object");
        };
        assert_with_mod(&struct_obj.name, "Nat", "Struct");
    }

    #[test]
    fn module_qualification_preserves_explicit_reference_module_names() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by thm Other::T(a)");
        let Stmt::By(ByStmt::ByThmStmt(thm_stmt)) = thm_stmt else {
            panic!("expected by thm stmt");
        };
        assert_with_mod(&thm_stmt.name, "Other", "T");

        let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Other::Template<2>");
        let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
            panic!("expected instantiated template object");
        };
        assert_with_mod(&template_obj.template_name, "Other", "Template");

        let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Other::Struct");
        let Obj::StructObj(struct_obj) = struct_obj else {
            panic!("expected struct object");
        };
        assert_with_mod(&struct_obj.name, "Other", "Struct");
    }

    #[test]
    fn standard_library_namespace_is_valid_only_as_a_qualified_module_root() {
        let mut rt = Runtime::new();

        let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by thm basics::T(a)");
        let Stmt::By(ByStmt::ByThmStmt(thm_stmt)) = thm_stmt else {
            panic!("expected by thm stmt");
        };
        assert_with_mod(&thm_stmt.name, "basics::implementation", "T");

        let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\basics::Template<2>");
        let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
            panic!("expected instantiated template object");
        };
        assert_with_mod(
            &template_obj.template_name,
            "basics::implementation",
            "Template",
        );

        let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&basics::Struct");
        let Obj::StructObj(struct_obj) = struct_obj else {
            panic!("expected struct object");
        };
        assert_with_mod(&struct_obj.name, "basics::implementation", "Struct");

        let replacement_obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(basics::P, A)");
        let Obj::Replacement(replacement_obj) = replacement_obj else {
            panic!("expected replacement object");
        };
        assert_with_mod(&replacement_obj.prop_name, "basics::implementation", "P");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "basics::value");
        let Obj::Atom(AtomObj::IdentifierWithMod(obj)) = obj else {
            panic!("expected module-qualified identifier");
        };
        assert_eq!(obj.mod_name, "basics::implementation");
        assert_eq!(obj.name, "value");

        let fact = parse_one_fact_line_with_runtime(&mut rt, "$basics::P(a)");
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) = fact else {
            panic!("expected normal atomic fact");
        };
        assert_with_mod(&fact.predicate, "basics::implementation", "P");

        let mut tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("by thm std(a)", Rc::from("test.lit"))
            .expect("tokenize theorem reference");
        assert_eq!(blocks.len(), 1);
        assert!(rt.parse_stmt(&mut blocks[0]).is_err());

        let mut blocks = tokenizer
            .parse_blocks("by thm Other::std::T(a)", Rc::from("test.lit"))
            .expect("tokenize nested module reference");
        assert_eq!(blocks.len(), 1);
        assert!(rt.parse_stmt(&mut blocks[0]).is_err());
    }

    #[test]
    fn module_qualification_preserves_explicit_module_names() {
        let mut rt = Runtime::new();
        set_test_module_name(&mut rt, "Nat");

        let obj = parse_one_obj_line_with_runtime(&mut rt, "Other::a");

        let Obj::Atom(AtomObj::IdentifierWithMod(id)) = obj else {
            panic!("expected module-qualified identifier");
        };
        assert_eq!(id.mod_name, "Other");
        assert_eq!(id.name, "a");
    }

    #[test]
    fn module_qualification_keeps_names_bare_without_module_context() {
        let mut rt = Runtime::new();

        let obj = parse_one_obj_line_with_runtime(&mut rt, "a");
        let Obj::Atom(AtomObj::Identifier(id)) = obj else {
            panic!("expected bare identifier");
        };
        assert_eq!(id.name, "a");

        let fact = parse_one_fact_line_with_runtime(&mut rt, "$some_prop(a)");
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(atomic_fact)) = fact else {
            panic!("expected normal atomic fact");
        };
        let AtomicName::WithoutMod(name) = &atomic_fact.predicate else {
            panic!("expected bare predicate");
        };
        assert_eq!(name, "some_prop");

        let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by thm T(a)");
        let Stmt::By(ByStmt::ByThmStmt(thm_stmt)) = thm_stmt else {
            panic!("expected by thm stmt");
        };
        assert_without_mod(&thm_stmt.name, "T");

        let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Template<2>");
        let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
            panic!("expected instantiated template object");
        };
        assert_without_mod(&template_obj.template_name, "Template");

        let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Struct");
        let Obj::StructObj(struct_obj) = struct_obj else {
            panic!("expected struct object");
        };
        assert_without_mod(&struct_obj.name, "Struct");
    }
}
