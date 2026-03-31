use crate::prelude::*;

impl Runtime {
    pub fn parse_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.parse_obj_hierarchy0(tb)
    }

    /// 中缀 \ 最松散；往下依次为 +-、*/%、^、[]、主元
    fn parse_obj_hierarchy0(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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
                    _ => Err(ParsingError::new(
                        format!("{} does not support infix function syntax", fn_name),
                        tb.line_file,
                        None,
                    )),
                };
            }

            let body = vec![vec![Box::new(left), Box::new(right)]];

            Ok(Obj::FnObj(FnObj::new(fn_name, body)))
        } else {
            Ok(left)
        }
    }

    /// + - 优先级最低，左结合，可连续 2 + 3 - 4
    fn parse_obj_hierarchy1(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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
    fn parse_obj_hierarchy2(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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
    fn parse_obj_hierarchy3(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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
    fn parse_obj_hierarchy4(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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

    /// 主元：{ }、@、fn、数字、括号、关键字、atom
    fn parse_obj_hierarchy5(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        if tb.current_token_is_equal_to(LEFT_CURLY_BRACE) {
            self.parse_set_builder_or_set_list(tb)
        } else if tb.current_token_is_equal_to(FN_FOR_FN_WITH_PARAMS) {
            tb.skip_token(FN_FOR_FN_WITH_PARAMS)?;
            Ok(Obj::FnSetWithParams(
                self.parse_fn_set_with_dom_without_fn_prefix(tb)?,
            ))
        } else {
            self.parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(tb)
        }
    }

    pub fn parse_fn_set_with_dom_without_fn_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<FnSetWithParams, ParsingError> {
        self.push_parsing_time_name_scope();
        let fn_set = self.parse_fn_set_with_dom_without_fn_prefix_body(tb);
        self.pop_parsing_time_name_scope();
        fn_set
    }

    fn parse_fn_set_with_dom_without_fn_prefix_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<FnSetWithParams, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_set: Vec<ParamDefWithParamSet> = vec![];
        loop {
            let param = tb.advance()?;
            let mut current_params = vec![param];

            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                current_params.push(tb.advance()?);
            }

            let set = self.parse_obj(tb)?;
            params_def_with_set.push(ParamDefWithParamSet(current_params, set));
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                continue;
            } else if tb.current_token_is_equal_to(COLON) {
                break;
            } else if tb.current_token_is_equal_to(RIGHT_BRACE) {
                break;
            } else {
                return Err(ParsingError::new(
                    "Expected comma or colon".to_string(),
                    tb.line_file,
                    None,
                ));
            }
        }

        let fn_set_param_names = ParamDefWithParamSet::collect_param_names(&params_def_with_set);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &fn_set_param_names,
            tb.line_file,
        )
        .map_err(|e| {
            ParsingError::new(
                e.to_string(),
                tb.line_file,
                Some(RuntimeError::ParseBlockError(e)),
            )
        })?;

        let mut dom_facts = vec![];
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            dom_facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                dom_facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
            }
        }

        tb.skip_token(RIGHT_BRACE)?;
        let ret_set = self.parse_obj(tb)?;
        Ok(FnSetWithParams::new(
            params_def_with_set,
            dom_facts,
            ret_set,
        ))
    }

    pub fn parse_number_or_primary_obj_or_fn_obj_with_minus_prefix(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, ParsingError> {
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
    ) -> Result<Obj, ParsingError> {
        let token = tb.current()?;

        // 0. (obj) 或 (obj, obj, ...)
        if token == LEFT_BRACE {
            tb.skip()?;
            let obj = self.parse_obj(tb)?;

            if tb.current_token_is_equal_to(COMMA) {
                let mut args = vec![obj];
                tb.skip_token(COMMA)?;
                while !tb.current_token_is_equal_to(RIGHT_BRACE) {
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
                    return Err(ParsingError::new(
                        format!("Invalid number: {}", number),
                        tb.line_file,
                        None,
                    ));
                }
                return Ok(Obj::Number(Number::new(number)));
            }

            if tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let fraction = tb.advance()?;
                let number = format!("{}{}{}", number, DOT_AKA_FIELD_ACCESS_SIGN, fraction);
                if !is_number(&number) {
                    return Err(ParsingError::new(
                        format!("Invalid number: {}", number),
                        tb.line_file,
                        None,
                    ));
                }
                return Ok(Obj::Number(Number::new(number)));
            } else {
                if !is_number(&number) {
                    return Err(ParsingError::new(
                        format!("Invalid number: {}", number),
                        tb.line_file,
                        None,
                    ));
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
    fn parse_primary_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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

        // 多元关键字：吃关键字 + 括号里若干 obj
        if tok == UNION {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "union expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new("union expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new("union expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Union(Union::new(left, right)));
        }
        if tok == INTERSECT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new(
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new(
                    "intersect expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            return Ok(Obj::Intersect(Intersect::new(left, right)));
        }
        if tok == SET_MINUS {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new(
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new(
                    "set_minus expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            return Ok(Obj::SetMinus(SetMinus::new(left, right)));
        }
        if tok == SET_DIFF {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new(
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new(
                    "disjoint_union expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            return Ok(Obj::SetDiff(SetDiff::new(left, right)));
        }
        if tok == CAP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "cap expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("cap expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Cap(Cap::new(value)));
        }
        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "cup expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("cup expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Cup(Cup::new(value)));
        }
        if tok == CHOOSE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "choice expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("choice expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Choose(Choose::new(value)));
        }
        if tok == PROJ {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "proj expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new("proj expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new("proj expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Proj(Proj::new(left, right)));
        }
        if tok == RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "range expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new("range expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new("range expects 2 arguments".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Range(Range::new(left, right)));
        }
        if tok == CLOSED_RANGE {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 2 {
                return Err(ParsingError::new(
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let left = it.next().ok_or_else(|| {
                ParsingError::new(
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            let right = it.next().ok_or_else(|| {
                ParsingError::new(
                    "closed_range expects 2 arguments".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            return Ok(Obj::ClosedRange(ClosedRange::new(left, right)));
        }

        if tok == CUP {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "cup expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("cup expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Cup(Cup::new(value)));
        }
        if tok == POWER_SET {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "power_set expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new(
                    "power_set expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                )
            })?;
            return Ok(Obj::PowerSet(PowerSet::new(value)));
        }
        if tok == CART_DIM {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "set_dim expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("set_dim expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::CartDim(CartDim::new(value)));
        }
        if tok == COUNT {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
            if args.len() != 1 {
                return Err(ParsingError::new(
                    "count expects 1 argument".to_string(),
                    tb.line_file,
                    None,
                ));
            }
            let mut it = args.into_iter();
            let value = it.next().ok_or_else(|| {
                ParsingError::new("count expects 1 argument".to_string(), tb.line_file, None)
            })?;
            return Ok(Obj::Count(Count::new(value)));
        }
        if tok == CART {
            tb.skip()?;
            let args = self.parse_braced_objs(tb)?;
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

    pub fn parse_braced_objs(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    pub fn parse_braced_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let mut parsed_args = self.parse_braced_objs(tb)?;
        if parsed_args.len() != 1 {
            return Err(ParsingError::new(
                "expected exactly 1 argument".to_string(),
                tb.line_file,
                None,
            ));
        }
        let parsed_obj = parsed_args.remove(0);
        Ok(parsed_obj)
    }

    /// 解析逗号分隔的 obj 列表，直到遇到非 COMMA 的 token（如 COLON）。
    pub fn parse_obj_list(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        Ok(objs)
    }

    fn parse_set_builder_or_set_list(&mut self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
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
    ) -> Result<Obj, ParsingError> {
        self.push_parsing_time_name_scope();
        let result = self.parse_set_builder_body(tb, a);
        self.pop_parsing_time_name_scope();
        result
    }

    /// Parse after first identifier: either "S : fact1, fact2" (SetBuilder) or "b c" (ListSet).
    fn parse_set_builder_body(
        &mut self,
        tb: &mut TokenBlock,
        a: Identifier,
    ) -> Result<Obj, ParsingError> {
        self.validate_name_and_insert_into_top_parsing_time_name_scope(&a.name, tb.line_file)
            .map_err(|e| {
                ParsingError::new(
                    duplicate_used_name_error_msg_without_line_file(&a.name),
                    tb.line_file,
                    Some(RuntimeError::ParseBlockError(e)),
                )
            })?;

        let second = self.parse_obj(tb)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let mut facts = vec![];
            while tb.current()? != RIGHT_CURLY_BRACE {
                facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
            }
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            Ok(Obj::SetBuilder(SetBuilder::new(a.name, second, facts)))
        } else {
            let mut objs = Vec::with_capacity(2);
            objs.push(Obj::Identifier(a));
            objs.push(second);
            while tb.current()? != RIGHT_CURLY_BRACE {
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
                objs.push(self.parse_obj(tb)?);
            }
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            Ok(Obj::ListSet(ListSet::new(objs)))
        }
    }

    /// ListSet: { a b c } 或 { 1, 0, 2 }；遇逗号先 skip 再解析下一项
    fn parse_list_set_obj_with_leftmost_obj(
        &mut self,
        tb: &mut TokenBlock,
        left_most_obj: Obj,
    ) -> Result<Obj, ParsingError> {
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

    pub fn parse_list_set_obj(&mut self, tb: &mut TokenBlock) -> Result<ListSet, ParsingError> {
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

    pub fn parse_atom(&self, tb: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            tb.skip()?;
            let right = tb.advance()?;
            if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let mut fields = vec![tb.advance()?.to_string()];
                while !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                    tb.skip()?;
                    fields.push(tb.advance()?.to_string());
                }

                Ok(Atom::FieldAccessWithMod(FieldAccessWithMod::new(
                    left, right, fields,
                )))
            } else {
                Ok(Atom::IdentifierWithMod(IdentifierWithMod::new(left, right)))
            }
        } else {
            // 如果后面有 .，则解析为 FieldAccess
            if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let mut fields = vec![tb.advance()?.to_string()];
                while !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                    tb.skip()?;
                    fields.push(tb.advance()?.to_string());
                }
                Ok(Atom::FieldAccess(FieldAccess::new(left, fields)))
            } else {
                Ok(Atom::Identifier(Identifier::new(left)))
            }
        }
    }

    pub fn parse_identifier_or_identifier_with_mod(
        &self,
        tb: &mut TokenBlock,
    ) -> Result<IdentifierOrIdentifierWithMod, ParsingError> {
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
