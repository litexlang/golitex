use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        self.parse_obj_hierarchy0(tb)
    }

    /// Infix `name` (one backtick before the function name) is loosest; then `+-`, `*/%`, `^`, `[]`, `...`, primary.
    fn parse_obj_hierarchy0(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy1(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(INFIX_FN_NAME_SIGN) {
            tb.skip()?; // consume the infix delimiter, then read the name
            let fn_name = self.parse_identifier_or_identifier_with_mod(tb)?;
            let right = self.parse_obj(tb)?;

            if is_key_symbol_or_keyword(&fn_name.to_string()) {
                return match fn_name.to_string().as_str() {
                    UNION => Ok(Union::new(left, right).into()),
                    INTERSECT => Ok(Intersect::new(left, right).into()),
                    SET_MINUS => Ok(SetMinus::new(left, right).into()),
                    SET_DIFF => Ok(SetDiff::new(left, right).into()),
                    RANGE => Ok(Range::new(left, right).into()),
                    CLOSED_RANGE => Ok(ClosedRange::new(left, right).into()),
                    PROJ => Ok(Proj::new(left, right).into()),
                    _ => Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("{} does not support infix function syntax", fn_name),
                            tb.line_file.clone(),
                        ),
                    ))),
                };
            }

            let body = vec![vec![Box::new(left), Box::new(right)]];

            let head = FnObjHead::given_an_atom_return_a_fn_obj_head(fn_name).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("infix (backtick) expects an identifier or single field-access name for the function"
                        .to_string(), tb.line_file.clone())))
            })?;
            Ok(FnObj::new(head, body).into())
        } else {
            Ok(left)
        }
    }

    /// + - 优先级最低，左结合，可连续 2 + 3 - 4
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

    /// * / % 高于 + -，左结合
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

    /// ^ 高于 * / %，右结合：2^3^2 = 2^(3^2)
    fn parse_obj_hierarchy3(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy4(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(POW) {
            tb.skip()?;
            let right = self.parse_obj_hierarchy3(tb)?; // 右结合：右侧可继续接 ^
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
                return Ok(left);
            }
        }
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
        } else if tb.current_token_is_equal_to(FN_LOWER_CASE) {
            tb.skip_token(FN_LOWER_CASE)?;
            Ok(self.parse_fn_set(tb)?.into())
        } else if tb.current_token_is_equal_to(ANONYMOUS_FN_PREFIX) {
            let mut result = self.parse_anonymous_fn(tb)?;
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

    /// `'` + `(param sets [: dom])` + return set + `{ body }`, or `'` + set + `(names)` + `{ body }`.
    ///
    /// After a comma-separated name list, if the next token is `:` (domain facts) rather than a set
    /// expression, parameters are taken to be in `R` (same as writing `x, y R : ...`).
    pub fn parse_anonymous_fn(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        tb.skip_token(ANONYMOUS_FN_PREFIX)?;
        if tb.current_token_is_equal_to(LEFT_BRACE) {
            let built = self.run_in_local_parsing_time_name_scope(|this| {
                tb.skip_token(LEFT_BRACE)?;
                let mut params_def_with_set: Vec<ParamGroupWithSet> = vec![];
                loop {
                    let param = parse_synthetically_correct_identifier_string(tb)?;
                    let mut current_params = vec![param];

                    while tb.current_token_is_equal_to(COMMA) {
                        tb.skip_token(COMMA)?;
                        current_params.push(parse_synthetically_correct_identifier_string(tb)?);
                    }

                    let param_group = if tb.current_token_is_equal_to(COLON) {
                        ParamGroupWithSet::new(current_params, StandardSet::R.into())
                    } else {
                        ParamGroupWithSet::new(current_params, this.parse_obj(tb)?)
                    };
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
                            RuntimeErrorStruct::new_with_msg_and_line_file("anonymous fn: expected `,`, `:`, or closing `)` after parameter group"
                                    .to_string(), tb.line_file.clone()),
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
                let equal_to = this.parse_in_local_free_param_scope(
                    ParamObjType::FnSet,
                    &all_fn_names,
                    tb.line_file.clone(),
                    |inner| {
                        tb.skip_token(LEFT_CURLY_BRACE)?;
                        let equal_to = inner.parse_obj(tb)?;
                        tb.skip_token(RIGHT_CURLY_BRACE)?;
                        Ok(equal_to)
                    },
                )?;
                let built =
                    this.new_anonymous_fn(params_def_with_set, dom_facts, ret_set_parsed, equal_to)?;
                Ok(built)
            })?;
            Ok(built.into())
        } else {
            let set_obj = self.parse_and_reclassify_atom_as_free_param_obj(tb)?;
            let built = self.run_in_local_parsing_time_name_scope(|this| {
                tb.skip_token(LEFT_BRACE)?;
                let mut params = vec![parse_synthetically_correct_identifier_string(tb)?];
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    params.push(parse_synthetically_correct_identifier_string(tb)?);
                }
                tb.skip_token(RIGHT_BRACE)?;
                let param_group = ParamGroupWithSet::new(params, set_obj.clone());
                let param_groups = vec![param_group.clone()];
                let all_names = ParamGroupWithSet::collect_param_names(&param_groups);
                this.parsing_free_param_collection.begin_scope(
                    ParamObjType::FnSet,
                    &all_names,
                    tb.line_file.clone(),
                )?;
                tb.skip_token(LEFT_CURLY_BRACE)?;
                let equal_to = this.parse_obj(tb)?;
                tb.skip_token(RIGHT_CURLY_BRACE)?;
                this.parsing_free_param_collection
                    .end_scope(ParamObjType::FnSet, &all_names);
                this.new_anonymous_fn(vec![param_group], vec![], set_obj, equal_to)
            })?;
            Ok(built.into())
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

    /// 若得到 atom，调用方再给其接若干 (args) 变成 FnObj。
    fn parse_number_or_primary_obj_or_fn_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let token = tb.current()?;

        // 0. (obj) 或 (obj, obj, ...)
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

        // 1. 数字
        if starts_with_digit(token) {
            let number = tb.advance()?;
            // 若已经到行尾，则直接检查并返回
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

        // 2. 多元关键字、或 atom（内建 `StandardSet` 名在 reclassify 中处理）
        let mut result = self.parse_primary_obj(tb)?;

        // 3. 若是 atom，后面可以接多组 (args)，每组一个 Vec<Obj>，合起来 body: Vec<Vec<Box<Obj>>>
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
            Obj::Atom(AtomObj::DefStructField(_)) => return Ok(result),
            Obj::AnonymousFn(anon) => (
                FnObjHead::AnonymousFnLiteral(Box::new(anon.clone())),
                vec![],
            ),
            Obj::FiniteSeqListObj(list) => (FnObjHead::FiniteSeqListObj(list.clone()), vec![]),
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

    /// 解析「主元」：当前 token 必须是多元关键字、或普通标识符 (atom)（内建 `StandardSet` 名走 atom 路径）。
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

        // 多元关键字：吃关键字 + 括号里若干 obj
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
                        "disjoint_union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "disjoint_union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "disjoint_union expects 2 arguments".to_string(),
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
        if tok == CHOOSE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "choice expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "choice expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Choose::new(value).into());
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
        if tok == OO || tok == OC || tok == CO || tok == CC {
            let interval_kind = tok.to_string();
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{} expects 2 arguments", interval_kind),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{} expects 2 arguments", interval_kind),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{} expects 2 arguments", interval_kind),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return match interval_kind.as_str() {
                OO => Ok(IntervalObj::new_left_open_right_open(left, right).into()),
                OC => Ok(IntervalObj::new_left_open_right_closed(left, right).into()),
                CO => Ok(IntervalObj::new_left_closed_right_open(left, right).into()),
                CC => Ok(IntervalObj::new_left_closed_right_closed(left, right).into()),
                _ => unreachable!(),
            };
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
        if tok == COUNT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "count expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "count expects 1 argument".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            return Ok(Count::new(value).into());
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

    // parse_identifier_or_identifier_with_mod + reclassify (std sets + free params).
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
                Ok(self
                    .parsing_free_param_collection
                    .resolve_identifier_to_free_param_obj(&id.name))
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

    /// 解析逗号分隔的 obj 列表，直到遇到非 COMMA 的 token（如 COLON）。
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
        let template_name = tb.advance()?;
        is_valid_litex_name(&template_name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        tb.skip_token(LEFT_CURLY_BRACE)?;
        let mut args = Vec::new();
        if !tb.current_token_is_equal_to(RIGHT_CURLY_BRACE) {
            args.push(self.parse_obj(tb)?);
            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                args.push(self.parse_obj(tb)?);
            }
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
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
                        let f = this.parse_or_and_chain_atomic_fact(tb)?;
                        facts_inst.push(this.inst_or_and_chain_atomic_fact(
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

    /// ListSet: { a b c } 或 { 1, 0, 2 }；遇逗号先 skip 再解析下一项
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
        let left = parse_synthetically_correct_identifier_string(tb)?;
        tb.skip_token(MOD_SIGN)?;
        let right = parse_synthetically_correct_identifier_string(tb)?;
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
        let name = self.parse_name_with_or_without_mod(tb)?;
        let params = if !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
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

    fn parse_name_with_or_without_mod(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<NameWithOrWithoutMod, RuntimeError> {
        let name = self.parse_atomic_name(tb)?;
        Ok(match name {
            AtomicName::WithoutMod(name) => NameWithOrWithoutMod::WithoutMod(name),
            AtomicName::WithMod(mod_name, name) => NameWithOrWithoutMod::WithMod(mod_name, name),
        })
    }

    /// `ident` or `mod::ident` as a predicate/atomic name in parse position.
    pub fn parse_atomic_name(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip()?;
            let right = parse_synthetically_correct_identifier_string(tb)?;
            Ok(AtomicName::WithMod(left, right))
        } else {
            Ok(AtomicName::WithoutMod(left))
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
