use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        self.parse_obj_hierarchy0(tb)
    }

    /// Infix `\` is loosest; then `+-`, `*/%`, `^`, `[]`, `...`, primary.
    fn parse_obj_hierarchy0(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy1(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(INFIX_FN_NAME_SIGN) {
            tb.skip()?; // 先吃掉 \，再读中缀函数名
            let fn_name = self.parse_atom(tb)?;
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
                        RuntimeErrorStruct::new(
                            None,
                            format!("{} does not support infix function syntax", fn_name),
                            tb.line_file.clone(),
                            None,
                            vec![],
                        ),
                    ))),
                };
            }

            let body = vec![vec![Box::new(left), Box::new(right)]];

            let head = FnObjHead::from_name_obj(fn_name).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "infix `\\` expects an identifier or single field-access name for the function"
                            .to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                ))
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
                                RuntimeErrorStruct::new(
                                    None,
                                    "matrix literal: expected `[` after `,` between rows"
                                        .to_string(),
                                    tb.line_file.clone(),
                                    None,
                                    vec![],
                                ),
                            )));
                        }
                    } else if tb.current_token_is_equal_to(RIGHT_BRACKET) {
                        tb.skip_token(RIGHT_BRACKET)?;
                        return Ok(MatrixListObj::new(rows).into());
                    } else {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new(
                                None,
                                "matrix literal: expected `,` or closing `]`".to_string(),
                                tb.line_file.clone(),
                                None,
                                vec![],
                            ),
                        )));
                    }
                }
            } else if tb.current_token_is_equal_to(RIGHT_BRACKET) {
                tb.skip_token(RIGHT_BRACKET)?;
                Ok(FiniteSeqListObj::new(vec![]).into())
            } else {
                let mut objs = vec![self.parse_obj(tb)?];
                while tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    objs.push(self.parse_obj(tb)?);
                }
                tb.skip_token(RIGHT_BRACKET)?;
                Ok(FiniteSeqListObj::new(objs).into())
            }
        } else if tb.current_token_is_equal_to(FN_LOWER_CASE) {
            tb.skip_token(FN_LOWER_CASE)?;
            Ok(self.parse_fn_set(tb)?.into())
        } else if tb.current_token_is_equal_to(ANONYMOUS_FN_PREFIX) {
            self.parse_anonymous_fn(tb)
        } else {
            self.parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(tb)
        }
    }

    /// `'` + `(param sets [: dom])` + return set + `{ body }`, or `'` + set + `(names)` + `{ body }`.
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

                    let set = this.parse_obj(tb)?;

                    params_def_with_set.push(ParamGroupWithSet::new(current_params, set));

                    if tb.current_token_is_equal_to(COMMA) {
                        tb.skip_token(COMMA)?;
                        continue;
                    } else if tb.current_token_is_equal_to(COLON) {
                        break;
                    } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                        break;
                    } else {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new(
                                None,
                                "anonymous fn: expected `,`, `:`, or closing `)` after parameter group"
                                    .to_string(),
                                tb.line_file.clone(),
                                None,
                                vec![],
                            ),
                        )));
                    }
                }

                let all_fn_names = ParamGroupWithSet::collect_param_names(&params_def_with_set);
                this.parsing_free_param_collection.begin_scope(
                    ParamObjType::AnonymousFn,
                    &all_fn_names,
                    tb.line_file.clone(),
                )?;

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
                let ret_set_parsed = this.parse_obj(tb)?;
                tb.skip_token(LEFT_CURLY_BRACE)?;
                let equal_to = this.parse_obj(tb)?;
                tb.skip_token(RIGHT_CURLY_BRACE)?;
                let built =
                    this.new_anonymous_fn(params_def_with_set, dom_facts, ret_set_parsed, equal_to)?;
                this.parsing_free_param_collection
                    .end_scope(ParamObjType::AnonymousFn, &all_fn_names);
                Ok(built)
            })?;
            Ok(built.into())
        } else {
            let set_obj = {
                let atom = self.parse_atom(tb)?;
                self.reclassify_atom_as_free_param_obj(atom)?
            };
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
                    ParamObjType::AnonymousFn,
                    &all_names,
                    tb.line_file.clone(),
                )?;
                tb.skip_token(LEFT_CURLY_BRACE)?;
                let equal_to = this.parse_obj(tb)?;
                tb.skip_token(RIGHT_CURLY_BRACE)?;
                this.parsing_free_param_collection
                    .end_scope(ParamObjType::AnonymousFn, &all_names);
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

                let set = this.parse_obj(tb)?;

                params_def_with_set.push(ParamGroupWithSet::new(current_params, set));

                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    continue;
                } else if tb.current_token_is_equal_to(COLON) {
                    break;
                } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                    break;
                } else {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "Expected comma or colon".to_string(),
                            tb.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
            }

            let all_fn_names = ParamGroupWithSet::collect_param_names(&params_def_with_set);
            this.parsing_free_param_collection.begin_scope(
                ParamObjType::FnSet,
                &all_fn_names,
                tb.line_file.clone(),
            )?;

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
            let ret_set_parsed = this.parse_obj(tb)?;
            let built = this.new_fn_set(params_def_with_set, dom_facts, ret_set_parsed);
            this.parsing_free_param_collection
                .end_scope(ParamObjType::FnSet, &all_fn_names);
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

                let set = this.parse_obj(tb)?;

                params_def_with_set.push(ParamGroupWithSet::new(current_params, set));

                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    continue;
                } else if tb.current_token_is_equal_to(COLON) {
                    break;
                } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                    break;
                } else {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "Expected comma or colon".to_string(),
                            tb.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
            }

            let all_fn_names = ParamGroupWithSet::collect_param_names(&params_def_with_set);
            this.parsing_free_param_collection.begin_scope(
                ParamObjType::FnSet,
                &all_fn_names,
                tb.line_file.clone(),
            )?;

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
            let ret_set_parsed = this.parse_obj(tb)?;
            let clause_ok = FnSetClause {
                params_def_with_set,
                dom_facts,
                ret_set: ret_set_parsed,
            };
            this.parsing_free_param_collection
                .end_scope(ParamObjType::FnSet, &all_fn_names);
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
                        RuntimeErrorStruct::new(
                            None,
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                            vec![],
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
                        RuntimeErrorStruct::new(
                            None,
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
                return Ok(Number::new(number).into());
            } else {
                if !is_number(&number) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
                return Ok(Number::new(number).into());
            }
        }

        // 2. 单符号集合、多元关键字、或 atom
        let mut result = self.parse_primary_obj(tb)?;

        // 3. 若是 atom，后面可以接多组 (args)，每组一个 Vec<Obj>，合起来 body: Vec<Vec<Box<Obj>>>
        let (head, mut body_vectors) = match &result {
            Obj::Atom(AtomObj::Identifier(i)) => (FnObjHead::Identifier(i.clone()), vec![]),
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => (FnObjHead::IdentifierWithMod(m.clone()), vec![]),
            Obj::Atom(AtomObj::Forall(p)) => (FnObjHead::Forall(p.clone()), vec![]),
            Obj::Atom(AtomObj::Exist(p)) => (FnObjHead::Exist(p.clone()), vec![]),
            Obj::Atom(AtomObj::Def(p)) => (FnObjHead::DefHeader(p.clone()), vec![]),
            Obj::Atom(AtomObj::SetBuilder(p)) => (FnObjHead::SetBuilder(p.clone()), vec![]),
            Obj::Atom(AtomObj::FnSet(p)) => (FnObjHead::FnSet(p.clone()), vec![]),
            Obj::Atom(AtomObj::AnonymousFn(p)) => (FnObjHead::AnonymousFnParam(p.clone()), vec![]),
            Obj::Atom(AtomObj::Induc(p)) => (FnObjHead::Induc(p.clone()), vec![]),
            Obj::Atom(AtomObj::DefAlgo(p)) => (FnObjHead::DefAlgo(p.clone()), vec![]),
            Obj::AnonymousFn(anon) => (
                FnObjHead::AnonymousFnLiteral(Box::new(anon.clone())),
                vec![],
            ),
            _ => return Ok(result),
        };
        while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
            let args = self.parse_braced_objs(tb)?;
            let group: Vec<Box<Obj>> = args.into_iter().map(Box::new).collect();
            body_vectors.push(group);
        }
        if !body_vectors.is_empty() {
            result = FnObj::new(head, body_vectors).into();
        }
        Ok(result)
    }

    /// 解析「主元」：当前 token 必须是单符号集合名、多元关键字、或普通标识符(atom)。
    fn parse_primary_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let tok = tb.current()?;

        // 单符号集合（无参）
        if tok == N_POS {
            tb.skip()?;
            return Ok(StandardSet::NPos.into());
        }
        if tok == N {
            tb.skip()?;
            return Ok(StandardSet::N.into());
        }
        if tok == Q {
            tb.skip()?;
            return Ok(StandardSet::Q.into());
        }
        if tok == Z {
            tb.skip()?;
            return Ok(StandardSet::Z.into());
        }
        if tok == R {
            tb.skip()?;
            return Ok(StandardSet::R.into());
        }
        if tok == Q_POS {
            tb.skip()?;
            return Ok(StandardSet::QPos.into());
        }
        if tok == R_POS {
            tb.skip()?;
            return Ok(StandardSet::RPos.into());
        }
        if tok == Q_NEG {
            tb.skip()?;
            return Ok(StandardSet::QNeg.into());
        }
        if tok == Z_NEG {
            tb.skip()?;
            return Ok(StandardSet::ZNeg.into());
        }
        if tok == R_NEG {
            tb.skip()?;
            return Ok(StandardSet::RNeg.into());
        }
        if tok == Q_NZ {
            tb.skip()?;
            return Ok(StandardSet::QNz.into());
        }
        if tok == Z_NZ {
            tb.skip()?;
            return Ok(StandardSet::ZNz.into());
        }
        if tok == R_NZ {
            tb.skip()?;
            return Ok(StandardSet::RNz.into());
        }

        if tok == FAMILY_OBJ_PREFIX {
            let family = self.parse_family_obj(tb)?;
            return Ok(Obj::FamilyObj(family));
        }
        if tok == ABS {
            tb.skip()?;
            tb.skip_token(LEFT_BRACE)?;
            let arg = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(Abs::new(arg).into());
        }
        if tok == MAX {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "max expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "max expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "max expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Max::new(left, right).into());
        }
        if tok == MIN {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "min expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "min expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "min expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Min::new(left, right).into());
        }
        if tok == LOG {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "log expects 2 arguments (base, argument)".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let base = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "log expects 2 arguments (base, argument)".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let arg = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "log expects 2 arguments (base, argument)".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Log::new(base, arg).into());
        }

        // 多元关键字：吃关键字 + 括号里若干 obj
        if tok == UNION {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Union::new(left, right).into());
        }
        if tok == INTERSECT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "intersect expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Intersect::new(left, right).into());
        }
        if tok == SET_MINUS {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "set_minus expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(SetMinus::new(left, right).into());
        }
        if tok == SET_DIFF {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "disjoint_union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(SetDiff::new(left, right).into());
        }
        if tok == CAP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "cap expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "cap expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Cap::new(value).into());
        }
        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "cup expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Cup::new(value).into());
        }
        if tok == CHOOSE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "choice expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "choice expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Choose::new(value).into());
        }
        if tok == PROJ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "proj expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "proj expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "proj expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Proj::new(left, right).into());
        }
        if tok == RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Range::new(left, right).into());
        }
        if tok == CLOSED_RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "closed_range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(ClosedRange::new(left, right).into());
        }
        if tok == FINITE_SEQ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "finite_seq expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "finite_seq expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let n = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "finite_seq expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(FiniteSeqSet::new(set, n).into());
        }
        if tok == SEQ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "seq expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let set = args.into_iter().next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "seq expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(SeqSet::new(set).into());
        }
        if tok == MATRIX {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 3 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "matrix expects 3 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let set = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "matrix expects 3 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let row_len = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "matrix expects 3 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let col_len = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "matrix expects 3 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(MatrixSet::new(set, row_len, col_len).into());
        }

        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "cup expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Cup::new(value).into());
        }
        if tok == POWER_SET {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "power_set expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "power_set expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(PowerSet::new(value).into());
        }
        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "set_dim expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "set_dim expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(CartDim::new(value).into());
        }
        if tok == COUNT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "count expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "count expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            return Ok(Count::new(value).into());
        }
        if tok == CART {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() < 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "cart expects at least 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                        vec![],
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

        // Ordinary atom (identifier): resolve free-param scope without building `Obj::Identifier` first.
        let atom = self.parse_atom(tb)?;

        self.reclassify_atom_as_free_param_obj(atom)
    }

    fn reclassify_atom_as_free_param_obj(&self, obj: Obj) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Atom(AtomObj::Identifier(id)) => {
                if id.name == SELF {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "`self` is not supported in this version".to_string(),
                            default_line_file(),
                            None,
                            vec![],
                        ),
                    )));
                }
                Ok(self
                    .parsing_free_param_collection
                    .resolve_identifier_to_free_param_obj(&id.name))
            }
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => Ok(Obj::Atom(AtomObj::IdentifierWithMod(m))),
            _ => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "internal: atom position was not a name form".to_string(),
                    default_line_file(),
                    None,
                    vec![],
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

    pub fn parse_braced_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parsed_args = self.parse_braced_objs(tb)?;
        if parsed_args.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "expected exactly 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
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

                    Ok(SetBuilder::new(a.name.clone(), second_inst, facts_inst).into())
                } else {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "expected colon after first argument".to_string(),
                            tb.line_file.clone(),
                            None,
                            vec![],
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

    /// Unqualified name-shaped atom. Field access (`name.field`) is not supported.
    pub fn parse_identifier_or_field_access(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "field access (`name.field`) is not supported in this version".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        Ok(Identifier::new(left).into())
    }

    fn parse_mod_qualified_atom(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = parse_synthetically_correct_identifier_string(tb)?;
        tb.skip_token(MOD_SIGN)?;
        let right = parse_synthetically_correct_identifier_string(tb)?;
        if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "field access on module-qualified names is not supported in this version"
                    .to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        Ok(IdentifierWithMod::new(left, right).into())
    }

    /// Unqualified or `::`-qualified name / field name; returns a name-shaped [`Obj`].
    pub fn parse_atom(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let next_is_mod = tb.token_at_add_index(1) == MOD_SIGN;
        if next_is_mod {
            self.parse_mod_qualified_atom(tb)
        } else {
            self.parse_identifier_or_field_access(tb)
        }
    }

    pub fn parse_predicate(&mut self, tb: &mut TokenBlock) -> Result<AtomicName, RuntimeError> {
        self.parse_atomic_name(tb)
    }

    pub fn parse_family_obj(&mut self, tb: &mut TokenBlock) -> Result<FamilyObj, RuntimeError> {
        tb.skip_token(FAMILY_OBJ_PREFIX)?;
        let name = self.parse_atomic_name(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(FamilyObj { name, params })
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
            RuntimeErrorStruct::new(
                None,
                format!("{} is not a valid identifier", cur),
                tb.line_file.clone(),
                None,
                vec![],
            ),
        )));
    }

    Ok(cur)
}
