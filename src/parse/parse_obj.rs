use crate::prelude::*;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        self.parse_obj_hierarchy0(tb)
    }

    /// 中缀 \ 最松散；往下依次为 +-、*/%、^、[]、主元
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
                    UNION => Ok(Obj::Union(Union::new(left, right))),
                    INTERSECT => Ok(Obj::Intersect(Intersect::new(left, right))),
                    SET_MINUS => Ok(Obj::SetMinus(SetMinus::new(left, right))),
                    SET_DIFF => Ok(Obj::SetDiff(SetDiff::new(left, right))),
                    RANGE => Ok(Obj::Range(Range::new(left, right))),
                    CLOSED_RANGE => Ok(Obj::ClosedRange(ClosedRange::new(left, right))),
                    PROJ => Ok(Obj::Proj(Proj::new(left, right))),
                    _ => Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            format!("{} does not support infix function syntax", fn_name),
                            tb.line_file.clone(),
                            None,
                        ),
                    ),
                };
            }

            let body = vec![vec![Box::new(left), Box::new(right)]];

            Ok(Obj::FnObj(FnObj::new(fn_name, body)))
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

                left = Obj::Add(Add::new(left, right));
            } else if tb.current_token_is_equal_to(SUB) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy2(tb)?;
                left = Obj::Sub(Sub::new(left, right));
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
                left = Obj::Mul(Mul::new(left, right));
            } else if tb.current_token_is_equal_to(DIV) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = Obj::Div(Div::new(left, right));
            } else if tb.current_token_is_equal_to(MOD) {
                tb.skip()?;
                let right = self.parse_obj_hierarchy3(tb)?;
                left = Obj::Mod(Mod::new(left, right));
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
            Ok(Obj::Pow(Pow::new(left, right)))
        } else {
            Ok(left)
        }
    }

    /// [] 下标，优先级高于 ^
    fn parse_obj_hierarchy4(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let left = self.parse_obj_hierarchy5(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        if tb.current_token_is_equal_to(LEFT_BRACKET) {
            tb.skip_token(LEFT_BRACKET)?;
            let obj = self.parse_obj(tb)?;
            tb.skip_token(RIGHT_BRACKET)?;
            Ok(Obj::ObjAtIndex(ObjAtIndex::new(left, obj)))
        } else {
            Ok(left)
        }
    }

    /// 主元：{ }、fn、数字、括号、关键字、atom
    fn parse_obj_hierarchy5(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        if tb.current_token_is_equal_to(LEFT_CURLY_BRACE) {
            self.parse_set_builder_or_set_list(tb)
        } else if tb.current_token_is_equal_to(FN_LOWER_CASE) {
            tb.skip_token(FN_LOWER_CASE)?;
            Ok(Obj::FnSet(self.parse_fn_set(tb)?))
        } else if tb.current_token_is_equal_to(FN_UPPER_CASE) {
            Ok(Obj::FnSet(self.parse_fn_upper_case_fn_set(tb)?))
        } else {
            self.parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(tb)
        }
    }

    /// `Fn (A, B, ...) R` 语法糖：等价于 `fn { __x1 A, __x2 B, ... } R`（`_i` 为未占用新名），无 dom 条件。
    fn parse_fn_upper_case_fn_set(&mut self, tb: &mut TokenBlock) -> Result<FnSet, RuntimeError> {
        tb.skip_token(FN_UPPER_CASE)?;
        tb.skip_token(LEFT_BRACE)?;
        let mut domain_sets: Vec<Obj> = Vec::new();
        if !tb.current_token_is_equal_to(RIGHT_BRACE) {
            loop {
                domain_sets.push(self.parse_obj(tb)?);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                    if tb.current_token_is_equal_to(RIGHT_BRACE) {
                        break;
                    }
                    continue;
                }
                break;
            }
        }
        tb.skip_token(RIGHT_BRACE)?;
        if domain_sets.is_empty() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "Fn(...) requires at least one domain type in parentheses".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
        let ret_set = self.parse_obj(tb)?;
        let names = self.generate_random_unused_names(domain_sets.len());
        let mut params_def_with_set: Vec<ParamGroupWithSet> = Vec::with_capacity(domain_sets.len());
        for (name, set) in names.into_iter().zip(domain_sets.into_iter()) {
            params_def_with_set.push(ParamGroupWithSet::new(vec![name], set));
        }
        self.new_fn_set_and_add_mangled_prefix(params_def_with_set, vec![], ret_set)
    }

    pub fn parse_fn_set(&mut self, tb: &mut TokenBlock) -> Result<FnSet, RuntimeError> {
        let fn_set = self.run_in_local_parsing_time_name_scope(|this| this.parse_fn_set_body(tb, true));
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
        let clause =
            self.run_in_local_parsing_time_name_scope(|this| this.parse_fn_set_body(tb, false));
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

    fn parse_fn_set_body(
        &mut self,
        tb: &mut TokenBlock,
        true_when_return_fn_set_false_when_return_fn_set_clause: bool,
    ) -> Result<FnSetOrFnSetClause, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_set: Vec<ParamGroupWithSet> = vec![];
        loop {
            let param = tb.advance()?;
            let mut current_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                current_params.push(tb.advance()?);
            }

            let set = self.parse_obj(tb)?;

            for p in current_params.clone().iter() {
                if !true_when_return_fn_set_false_when_return_fn_set_clause {
                    // 这里需要register一下，因为后文可能会用到这些参数
                    self.register_name_into_name_scope(p, tb.line_file.clone())?;
                } else {
                    if !is_valid_litex_name(&p).is_ok() {
                        return Err(
                            RuntimeError::new_parse_error_with_msg_position_previous_error(
                                format!("Invalid parameter name: {}", p),
                                tb.line_file.clone(),
                                None,
                            ),
                        );
                    }
                }

                let p_with_prefix = format!("{}{}", DEFAULT_MANGLED_FN_PARAM_PREFIX, p);
                self.register_name_into_name_scope(&p_with_prefix, tb.line_file.clone())?;
            }

            params_def_with_set.push(ParamGroupWithSet::new(current_params, set));

            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                continue;
            } else if tb.current_token_is_equal_to(COLON) {
                break;
            } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                break;
            } else {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "Expected comma or colon".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
        }

        let mut dom_facts = vec![];
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let cur = self.parse_or_and_chain_atomic_fact(tb)?;
            dom_facts.push(cur);
            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                let cur = self.parse_or_and_chain_atomic_fact(tb)?;
                dom_facts.push(cur);
            }
        }

        tb.skip_token(RIGHT_BRACE)?;
        let ret_set_parsed = self.parse_obj(tb)?;
        if true_when_return_fn_set_false_when_return_fn_set_clause {
            Ok(FnSetOrFnSetClause::FnSet(
                self.new_fn_set_and_add_mangled_prefix(
                    params_def_with_set,
                    dom_facts,
                    ret_set_parsed,
                )?,
            ))
        } else {
            Ok(FnSetOrFnSetClause::FnSetClause(FnSetClause {
                params_def_with_set,
                dom_facts,
                ret_set: ret_set_parsed,
            }))
        }
    }

    pub fn parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        if tb.current_token_is_equal_to(SUB) {
            tb.skip()?;
            let obj = self.parse_number_or_primary_obj_or_fn_obj(tb)?;
            Ok(Obj::Mul(Mul::new(
                Obj::Number(Number::new("-1".to_string())),
                obj,
            )))
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
                return Ok(Obj::Tuple(Tuple::new(args)));
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
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                        ),
                    );
                }
                return Ok(Obj::Number(Number::new(number)));
            }

            if tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let fraction = tb.advance()?;
                let number = format!("{}{}{}", number, DOT_AKA_FIELD_ACCESS_SIGN, fraction);
                if !is_number(&number) {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                        ),
                    );
                }
                return Ok(Obj::Number(Number::new(number)));
            } else {
                if !is_number(&number) {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            format!("Invalid number: {}", number),
                            tb.line_file.clone(),
                            None,
                        ),
                    );
                }
                return Ok(Obj::Number(Number::new(number)));
            }
        }

        // 2. 单符号集合、多元关键字、或 atom
        let mut result = self.parse_primary_obj(tb)?;

        // 3. 若是 atom，后面可以接多组 (args)，每组一个 Vec<Obj>，合起来 body: Vec<Vec<Box<Obj>>>
        let (head_atom, mut body_vectors) = match &result {
            Obj::Identifier(i) => (Atom::Identifier(i.clone()), vec![]),
            Obj::IdentifierWithMod(m) => (Atom::IdentifierWithMod(m.clone()), vec![]),
            Obj::FieldAccess(field_access) => (Atom::FieldAccess(field_access.clone()), vec![]),
            Obj::FieldAccessWithMod(field_access_with_mod) => (
                Atom::FieldAccessWithMod(field_access_with_mod.clone()),
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
            result = Obj::FnObj(FnObj::new(head_atom, body_vectors));
        }
        Ok(result)
    }

    /// 解析「主元」：当前 token 必须是单符号集合名、多元关键字、或普通标识符(atom)。
    fn parse_primary_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let tok = tb.current()?;

        // 单符号集合（无参）
        if tok == N_POS {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::NPos));
        }
        if tok == N {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::N));
        }
        if tok == Q {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::Q));
        }
        if tok == Z {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::Z));
        }
        if tok == R {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::R));
        }
        if tok == Q_POS {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::QPos));
        }
        if tok == R_POS {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::RPos));
        }
        if tok == Q_NEG {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::QNeg));
        }
        if tok == Z_NEG {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::ZNeg));
        }
        if tok == R_NEG {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::RNeg));
        }
        if tok == Q_NZ {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::QNz));
        }
        if tok == Z_NZ {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::ZNz));
        }
        if tok == R_NZ {
            tb.skip()?;
            return Ok(Obj::StandardSet(StandardSet::RNz));
        }

        if tok == FAMILY {
            let family = self.parse_family_obj(tb)?;
            return Ok(Obj::FamilyObj(family));
        }
        if tok == STRUCT {
            let struct_obj = self.parse_struct_obj(tb)?;
            return Ok(Obj::StructObj(struct_obj.into()));
        }

        // 多元关键字：吃关键字 + 括号里若干 obj
        if tok == UNION {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Union(Union::new(left, right)));
        }
        if tok == INTERSECT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "intersect expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Intersect(Intersect::new(left, right)));
        }
        if tok == SET_MINUS {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "set_minus expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::SetMinus(SetMinus::new(left, right)));
        }
        if tok == SET_DIFF {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "disjoint_union expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::SetDiff(SetDiff::new(left, right)));
        }
        if tok == CAP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "cap expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "cap expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Cap(Cap::new(value)));
        }
        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "cup expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Cup(Cup::new(value)));
        }
        if tok == CHOOSE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "choice expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "choice expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Choose(Choose::new(value)));
        }
        if tok == PROJ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "proj expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "proj expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "proj expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Proj(Proj::new(left, right)));
        }
        if tok == RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Range(Range::new(left, right)));
        }
        if tok == CLOSED_RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "closed_range expects 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::ClosedRange(ClosedRange::new(left, right)));
        }

        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "cup expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "cup expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Cup(Cup::new(value)));
        }
        if tok == POWER_SET {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "power_set expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "power_set expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::PowerSet(PowerSet::new(value)));
        }
        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "set_dim expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "set_dim expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::CartDim(CartDim::new(value)));
        }
        if tok == COUNT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "count expects 1 argument".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "count expects 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;
            return Ok(Obj::Count(Count::new(value)));
        }
        if tok == CART {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() < 2 {
                return Err(
                    RuntimeError::new_parse_error_with_msg_position_previous_error(
                        "cart expects at least 2 arguments".to_string(),
                        tb.line_file.clone(),
                        None,
                    ),
                );
            }
            return Ok(Obj::Cart(Cart::new(args)));
        }

        if tok == TUPLE_DIM {
            tb.skip()?;
            let args = self.parse_braced_obj(tb)?;
            return Ok(Obj::TupleDim(TupleDim::new(args)));
        }

        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_obj(tb)?;
            return Ok(Obj::CartDim(CartDim::new(args)));
        }

        // 普通 atom（标识符）
        let atom = self.parse_atom(tb)?;
        return Ok(Obj::from(atom));
    }

    pub fn parse_braced_objs(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
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
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "expected exactly 1 argument".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
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
            return Ok(Obj::ListSet(ListSet::new(vec![])));
        }

        let left = self.parse_obj(tb)?;
        match left {
            Obj::Identifier(a) => {
                if tb.current_token_is_equal_to(COMMA) || tb.current()? == RIGHT_CURLY_BRACE {
                    self.parse_list_set_obj_with_leftmost_obj(tb, Obj::Identifier(a))
                } else {
                    self.parse_set_builder(tb, a)
                }
            }
            _ => self.parse_list_set_obj_with_leftmost_obj(tb, left),
        }
    }

    /// Parse set builder or list set after the first identifier; wraps body in a name block for the bound variable.
    fn parse_set_builder(
        &mut self,
        tb: &mut TokenBlock,
        a: Identifier,
    ) -> Result<Obj, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| this.parse_set_builder_body(tb, a))
    }

    /// Parse after first identifier: either "S : fact1, fact2" (SetBuilder) or "b c" (ListSet).
    fn parse_set_builder_body(
        &mut self,
        tb: &mut TokenBlock,
        a: Identifier,
    ) -> Result<Obj, RuntimeError> {
        let second = self.parse_obj(tb)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;

            // 先登记形参 mangling，再解析域与条件（与 fn 集一致：先绑定再读体）
            let user_names = vec![a.name.clone()];
            let (mangled_names, param_arg_map) =
                self.register_mangled_fn_param_binding(&user_names, tb.line_file.clone())?;
            let stored = mangled_names[0].clone();
            let second_inst = self.inst_obj(&second, &param_arg_map)?;

            let mut facts_inst = Vec::new();
            while tb.current()? != RIGHT_CURLY_BRACE {
                let f = self.parse_or_and_chain_atomic_fact(tb)?;
                facts_inst.push(self.inst_or_and_chain_atomic_fact(&f, &param_arg_map)?);
            }
            tb.skip_token(RIGHT_CURLY_BRACE)?;

            Ok(Obj::SetBuilder(SetBuilder::new(
                stored,
                second_inst,
                facts_inst,
            )))
        } else {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "expected colon after first argument".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }
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
        Ok(Obj::ListSet(ListSet::new(objs)))
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

    pub fn parse_atom(&self, tb: &mut TokenBlock) -> Result<Atom, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip()?;
            let right = tb.advance()?;
            if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let field = tb.advance()?.to_string();
                if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "chained field access `a.b.c` is not supported; use at most one `.`"
                                .to_string(),
                            tb.line_file.clone(),
                            None,
                        ),
                    );
                }

                Ok(Atom::FieldAccessWithMod(FieldAccessWithMod::new(
                    left, right, field,
                )))
            } else {
                Ok(Atom::IdentifierWithMod(IdentifierWithMod::new(left, right)))
            }
        } else {
            // 如果后面有 .，则解析为 FieldAccess
            if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let field = tb.advance()?.to_string();
                if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                    return Err(
                        RuntimeError::new_parse_error_with_msg_position_previous_error(
                            "chained field access `a.b.c` is not supported; use at most one `.`"
                                .to_string(),
                            tb.line_file.clone(),
                            None,
                        ),
                    );
                }
                Ok(Atom::FieldAccess(FieldAccess::new(left, field)))
            } else {
                Ok(Atom::Identifier(Identifier::new(left)))
            }
        }
    }

    pub fn parse_identifier_or_identifier_with_mod(
        &self,
        tb: &mut TokenBlock,
    ) -> Result<IdentifierOrIdentifierWithMod, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip()?;
            let right = tb.advance()?;
            Ok(IdentifierOrIdentifierWithMod::IdentifierWithMod(
                IdentifierWithMod::new(left, right),
            ))
        } else {
            Ok(IdentifierOrIdentifierWithMod::Identifier(Identifier::new(
                left,
            )))
        }
    }

    pub fn parse_family_obj(&mut self, tb: &mut TokenBlock) -> Result<FamilyObj, RuntimeError> {
        tb.skip_token(FAMILY)?;
        let name = self.parse_identifier_or_identifier_with_mod(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(FamilyObj { name, params })
    }

    pub fn parse_struct_obj(&mut self, tb: &mut TokenBlock) -> Result<StructObj, RuntimeError> {
        tb.skip_token(STRUCT)?;
        let name = self.parse_identifier_or_identifier_with_mod(tb)?;
        let params = self.parse_braced_objs(tb)?;
        Ok(StructObj { name, args: params })
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
