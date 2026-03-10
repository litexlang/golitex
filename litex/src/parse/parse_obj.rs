use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::common::keywords::{
    ADD, CAP, CART, CART_DIM, CHOOSE, CLOSED_RANGE, COLON, COMMA, COUNT, CUP, SET_DIFF, DIV, DOT_AKA_FIELD_ACCESS_SIGN, FN, INFIX_FN_NAME_SIGN, INST_STRUCT_OBJ_SIGN, INTERSECT, LEFT_BRACE, LEFT_BRACKET, LEFT_CURLY_BRACE, MOD, MOD_SING, MUL, N, N_POS, POW, POWER_SET, PROJ, Q, Q_NEG, Q_NZ, Q_POS, R, R_NEG, R_NZ, R_POS, RANGE, RIGHT_BRACE, RIGHT_BRACKET, RIGHT_CURLY_BRACE, SET_MINUS, SUB, UNION, VAL, Z, Z_NEG, Z_NZ, Z_POS, is_key_symbol_or_keyword
};
use super::Parser;
use super::TokenBlock;
use crate::obj::{
    Obj, FnObj, FnSetObj, FnSetWithDom, FnSetWithoutDom, Add, Mul, Div, Mod, Sub, Pow, Number, InstStructObj, ListSet, SetBuilder,
    NPosObj, NObj, QObj, ZObj, RObj, QPos, ZPos, RPos, QNeg, ZNeg, RNeg, QNz, ZNz, RNz,
    ObjAtIndex, Union, Intersect, SetMinus, SetDiff, Cup, Cap, PowerSet, Choose,
    Cart, CartDim, Proj, Count, Range, ClosedRange, Val,
};
use crate::obj::{Atom, FieldAccess, FieldAccessWithMod, Identifier, IdentifierWithMod, IdentifierOrIdentifierWithMod};
use crate::error::ParsingError;
use crate::stmt::parameter_type_and_property::ParamDefWithParamSet;

impl Parser {
    pub fn obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.obj_hierarchy0(tb)
    }

    /// 中缀 \ 最松散；往下依次为 +-、*/%、^、[]、主元
    fn obj_hierarchy0(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy1(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            INFIX_FN_NAME_SIGN => {
                tb.skip()?; // 先吃掉 \，再读中缀函数名
                let fn_name = self.atom(tb)?;
                let right = self.obj(tb)?;

                if is_key_symbol_or_keyword(&fn_name.to_string()) {
                    return match fn_name.to_string().as_str() {
                        UNION => Ok(Obj::Union(Union::new(left, right))),
                        INTERSECT => Ok(Obj::Intersect(Intersect::new(left, right))),
                        SET_MINUS => Ok(Obj::SetMinus(SetMinus::new(left, right))),
                        SET_DIFF => Ok(Obj::SetDiff(SetDiff::new(left, right))),
                        RANGE => Ok(Obj::Range(Range::new(left, right))),
                        CLOSED_RANGE => Ok(Obj::ClosedRange(ClosedRange::new(left, right))),
                        PROJ => Ok(Obj::Proj(Proj::new(left, right))),
                        _ => Err(ParsingError::new(&format!("{} does not support infix function syntax", fn_name), tb.line_file_index)),
                    };
                }

                let head = Obj::from(fn_name);
                Ok(Obj::FnObj(FnObj::new(head, vec![left, right])))
            },
            _ => Ok(left),
        }
    }

    /// + - 优先级最低，左结合，可连续 2 + 3 - 4
    fn obj_hierarchy1(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let mut left = self.obj_hierarchy2(tb)?;
        loop {
            if tb.exceed_end_of_head() {
                return Ok(left);
            }
            match tb.current_token_empty_if_exceed_end_of_head() {
                ADD => {
                    tb.skip()?;
                    let right = self.obj_hierarchy2(tb)?;

                    let can_be_calculated = left.can_be_calculated() && right.can_be_calculated();
                    
                    left = Obj::Add(Add::new(left, right, can_be_calculated));
                },
                SUB => {
                    tb.skip()?;
                    let right = self.obj_hierarchy2(tb)?;
                    let can_be_calculated = left.can_be_calculated() && right.can_be_calculated();
                    left = Obj::Sub(Sub::new(left, right, can_be_calculated));
                },
                _ => return Ok(left),
            }
        }
    }

    /// * / % 高于 + -，左结合
    fn obj_hierarchy2(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let mut left = self.obj_hierarchy3(tb)?;
        loop {
            if tb.exceed_end_of_head() {
                return Ok(left);
            }
            match tb.current_token_empty_if_exceed_end_of_head() {
                MUL => {
                    tb.skip()?;
                    let right = self.obj_hierarchy3(tb)?;
                    let can_be_calculated = left.can_be_calculated() && right.can_be_calculated();
                    left = Obj::Mul(Mul::new(left, right, can_be_calculated));
                },
                DIV => {
                    tb.skip()?;
                    let right = self.obj_hierarchy3(tb)?;
                    left = Obj::Div(Div::new(left, right));
                },
                MOD => {
                    tb.skip()?;
                    let right = self.obj_hierarchy3(tb)?;

                    let mut can_be_calculated = true;
                    if !left.can_be_calculated() {
                        can_be_calculated = false;
                    }
                    if !right.can_be_calculated() {
                        can_be_calculated = false;
                    } else {
                        let calculated_right = right.calculate_to_string();
                        if is_number_string_literally_integer_without_dot(&calculated_right) {
                            can_be_calculated = false;
                        }
                    }
                    
                    left = Obj::Mod(Mod::new(left, right, can_be_calculated));
                },
                _ => return Ok(left),
            }
        }
    }

    /// ^ 高于 * / %，右结合：2^3^2 = 2^(3^2)
    fn obj_hierarchy3(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy4(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            POW => {
                tb.skip()?;
                let right = self.obj_hierarchy3(tb)?; // 右结合：右侧可继续接 ^
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Pow(Pow::new(left, right, false)))
                } else {
                    Ok(Obj::Pow(Pow::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    /// [] 下标，优先级高于 ^
    fn obj_hierarchy4(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy5(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            LEFT_BRACKET => {
                tb.skip_token(LEFT_BRACKET)?;
                let obj = self.obj(tb)?;
                tb.skip_token(RIGHT_BRACKET)?;
                Ok(Obj::ObjAtIndex(ObjAtIndex::new(left, obj)))
            }
            _ => Ok(left),
        }
    }

    /// 主元：{ }、@、fn、数字、括号、关键字、atom
    fn obj_hierarchy5(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        match tb.current_token_empty_if_exceed_end_of_head() {
            LEFT_CURLY_BRACE => {
                self.set_builder_or_set_list(tb)
            },
            INST_STRUCT_OBJ_SIGN => {
                self.instantiated_struct_obj(tb)
            },
            FN => {
                match self.fn_set_obj(tb)? {
                    FnSetObj::FnSetWithDom(fs) => Ok(Obj::FnSetWithDom(fs)),
                    FnSetObj::FnSetWithoutDom(fs) => Ok(Obj::FnSetWithoutDom(fs)),
                }
            },
            _ => self.number_or_primary_obj_or_fn_obj_with_minus_prefix(tb)
        }
    }

    pub fn fn_set_obj(&self, tb: &mut TokenBlock) -> Result<FnSetObj, ParsingError> {
        tb.skip_token(FN)?;
        self.fn_set_obj_without_prefix_fn(tb)
    }

    pub fn fn_set_obj_without_prefix_fn(&self, tb: &mut TokenBlock) -> Result<FnSetObj, ParsingError> {
        if tb.current()? != LEFT_BRACE {
            return Err(ParsingError::new("Expected left brace", tb.line_file_index));
        }
        
        let start = tb.parse_index + 1;
        let mut depth = 1;
        let mut i = start;
        while i < tb.header.len() {
            if tb.header[i] == LEFT_BRACE {
                depth += 1;
            } else if tb.header[i] == RIGHT_BRACE {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            i += 1;
        }
        let end = i;
        let has_colon = tb.header[start..end].iter().any(|t| t.as_str() == COLON);
        if has_colon {
            Ok(FnSetObj::FnSetWithDom(self.fn_set_with_dom_without_fn_prefix(tb)?))
        } else {
            Ok(FnSetObj::FnSetWithoutDom(self.fn_set_without_dom_without_fn_prefix(tb)?))
        }
    }

    pub fn fn_set_with_dom_without_fn_prefix(&self, tb: &mut TokenBlock) -> Result<FnSetWithDom, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut params_def_with_set: Vec<ParamDefWithParamSet> = vec![];
        loop {
            let param = tb.advance()?;
            let set = self.obj(tb)?;
            params_def_with_set.push(ParamDefWithParamSet(vec![param], set));
            if tb.current()? == COLON {
                break;
            }
            tb.skip_token(COMMA)?;
        }
        tb.skip_token(COLON)?;
        let mut dom_facts = vec![self.parse_matchable_fact_with_atomic_fact_inside(tb)?];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            dom_facts.push(self.parse_matchable_fact_with_atomic_fact_inside(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let ret_set = self.obj(tb)?;
        Ok(FnSetWithDom::new(params_def_with_set, dom_facts, ret_set))
    }

    pub fn fn_set_without_dom_without_fn_prefix(&self, tb: &mut TokenBlock) -> Result<FnSetWithoutDom, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut param_sets = vec![self.obj(tb)?];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            param_sets.push(self.obj(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let ret_set = self.obj(tb)?;
        Ok(FnSetWithoutDom::new(param_sets, ret_set))
    }

    pub fn number_or_primary_obj_or_fn_obj_with_minus_prefix(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        if tb.current_token_empty_if_exceed_end_of_head() == SUB {
            tb.skip()?;
            let obj = self.number_or_primary_obj_or_fn_obj(tb)?;
            Ok(Obj::Mul(Mul::new(Obj::Number(Number::new("-1")), obj, false)))
        } else {
            self.number_or_primary_obj_or_fn_obj(tb)
        }
    }

    /// 若得到 atom，调用方再给其接若干 (args) 变成 FnObj。
    fn number_or_primary_obj_or_fn_obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let token = tb.current()?;

        // 0. (obj)
        if token == LEFT_BRACE {
            tb.skip()?;
            let obj = self.obj(tb)?;
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(obj);
        }

        // 1. 数字
        if starts_with_digit(token) {
            let number = tb.advance()?;
            // 若已经到行尾，则直接检查并返回
            if tb.exceed_end_of_head() {
                if !is_number(&number) {
                    return Err(ParsingError::new(&format!("Invalid number: {}", number), tb.line_file_index));
                }
                return Ok(Obj::Number(Number::new(&number)));
            }

            if tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let fraction = tb.advance()?;
                let number = format!("{}{}{}", number, DOT_AKA_FIELD_ACCESS_SIGN, fraction);
                if !is_number(&number) {
                    return Err(ParsingError::new(&format!("Invalid number: {}", number), tb.line_file_index));
                }
                return Ok(Obj::Number(Number::new(&number)));
            } else {
                if !is_number(&number) {
                    return Err(ParsingError::new(&format!("Invalid number: {}", number), tb.line_file_index));
                }
                return Ok(Obj::Number(Number::new(&number)));
            }
        }

        // 2. 单符号集合、多元关键字、或 atom
        let mut result = self.parse_primary_obj(tb)?;

        // 3. 若是 atom，后面可以接多组 (args)，每组变成 FnObj(head, args)
        let is_atom = matches!(result, Obj::Identifier(_) | Obj::IdentifierWithMod(_));
        if is_atom {
            while !tb.exceed_end_of_head() && tb.current()? == LEFT_BRACE {
                let args = self.braced_objs(tb)?;
                result = Obj::FnObj(FnObj::new(result, args));
            }
        }
        Ok(result)
    }

    /// 解析「主元」：当前 token 必须是单符号集合名、多元关键字、或普通标识符(atom)。
    fn parse_primary_obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let tok = tb.current()?;

        // 单符号集合（无参）
        if tok == N_POS { tb.skip()?; return Ok(Obj::NPosObj(NPosObj::new())); }
        if tok == N { tb.skip()?; return Ok(Obj::NObj(NObj::new())); }
        if tok == Q { tb.skip()?; return Ok(Obj::QObj(QObj::new())); }
        if tok == Z { tb.skip()?; return Ok(Obj::ZObj(ZObj::new())); }
        if tok == R { tb.skip()?; return Ok(Obj::RObj(RObj::new())); }
        if tok == Q_POS { tb.skip()?; return Ok(Obj::QPos(QPos::new())); }
        if tok == Z_POS { tb.skip()?; return Ok(Obj::ZPos(ZPos::new())); }
        if tok == R_POS { tb.skip()?; return Ok(Obj::RPos(RPos::new())); }
        if tok == Q_NEG { tb.skip()?; return Ok(Obj::QNeg(QNeg::new())); }
        if tok == Z_NEG { tb.skip()?; return Ok(Obj::ZNeg(ZNeg::new())); }
        if tok == R_NEG { tb.skip()?; return Ok(Obj::RNeg(RNeg::new())); }
        if tok == Q_NZ { tb.skip()?; return Ok(Obj::QNz(QNz::new())); }
        if tok == Z_NZ { tb.skip()?; return Ok(Obj::ZNz(ZNz::new())); }
        if tok == R_NZ { tb.skip()?; return Ok(Obj::RNz(RNz::new())); }

        // 多元关键字：吃关键字 + 括号里若干 obj
        if tok == UNION {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("union expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Union(Union::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == INTERSECT {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("intersect expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Intersect(Intersect::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == SET_MINUS {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("set_minus expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::SetMinus(SetMinus::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == SET_DIFF {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("disjoint_union expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::SetDiff(SetDiff::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == CAP {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("cap expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::Cap(Cap::new(args.into_iter().next().unwrap())));
        }
        if tok == CHOOSE {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("choice expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::Choose(Choose::new(args.into_iter().next().unwrap())));
        }
        if tok == PROJ {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("proj expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Proj(Proj::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == RANGE {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("range expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Range(Range::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == CLOSED_RANGE {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("closed_range expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::ClosedRange(ClosedRange::new(it.next().unwrap(), it.next().unwrap())));
        }

        if tok == CUP {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("cup expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::Cup(Cup::new(args.into_iter().next().unwrap())));
        }
        if tok == POWER_SET {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("power_set expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::PowerSet(PowerSet::new(args.into_iter().next().unwrap())));
        }
        if tok == CART_DIM {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("set_dim expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::CartDim(CartDim::new(args.into_iter().next().unwrap())));
        }
        if tok == COUNT {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("count expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::Count(Count::new(args.into_iter().next().unwrap())));
        }
        if tok == VAL {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 1 { return Err(ParsingError::new("val expects 1 argument", tb.line_file_index)); }
            return Ok(Obj::Val(Val::new(args.into_iter().next().unwrap())));
        }

        if tok == CART {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            return Ok(Obj::Cart(Cart::new(args)));
        }

        // 普通 atom（标识符）
        let atom = self.atom(tb)?;
        Ok(Obj::from(atom))
    }

    pub fn braced_objs(&self, tb: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        tb.skip_token(LEFT_BRACE)?;
        let mut objs = vec![self.obj(tb)?];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            objs.push(self.obj(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    /// 解析逗号分隔的 obj 列表，直到遇到非 COMMA 的 token（如 COLON）。
    pub fn obj_list(&self, tb: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        let mut objs = vec![self.obj(tb)?];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            objs.push(self.obj(tb)?);
        }
        Ok(objs)
    }

    fn set_builder_or_set_list(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        tb.skip_token(LEFT_CURLY_BRACE)?;
        let left = self.obj(tb)?;
        match left {
            Obj::Identifier(a) => {
                if tb.current()? == COMMA || tb.current()? == RIGHT_CURLY_BRACE {
                    self.set_list(tb, Obj::Identifier(a))
                } else {
                    // 可能是 set builder "a S : ..." 或 list set "a b c"
                    let second = self.obj(tb)?;
                    if tb.current()? == COLON {
                        tb.skip_token(COLON)?;
                        let mut facts = vec![];
                        while tb.current()? != RIGHT_CURLY_BRACE {
                            facts.push(self.parse_matchable_fact_with_atomic_fact_inside(tb)?);
                            if tb.current()? == COMMA {
                                tb.skip_token(COMMA)?;
                            }
                        }
                        tb.skip_token(RIGHT_CURLY_BRACE)?;
                        Ok(Obj::SetBuilder(SetBuilder::new(a.name, second, facts)))
                    } else {
                        let mut objs = vec![Obj::Identifier(a), second];
                        while tb.current()? != RIGHT_CURLY_BRACE {
                            if tb.current()? == COMMA {
                                tb.skip_token(COMMA)?;
                            }
                            objs.push(self.obj(tb)?);
                        }
                        tb.skip_token(RIGHT_CURLY_BRACE)?;
                        Ok(Obj::ListSet(ListSet::new(objs)))
                    }
                }
            }
            _ => self.set_list(tb, left),
        }
    }

    /// ListSet: { a b c } 或 { 1, 0, 2 }；遇逗号先 skip 再解析下一项
    fn set_list(&self, tb: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        let mut objs = vec![left_most_obj];
        while tb.current()? != RIGHT_CURLY_BRACE {
            tb.skip_token(COMMA)?;
            objs.push(self.obj(tb)?);
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(Obj::ListSet(ListSet::new(objs)))
    }

    fn instantiated_struct_obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        tb.skip_token(INST_STRUCT_OBJ_SIGN)?;
        let name = self.identifier_or_identifier_with_mod(tb)?;
        let args = self.braced_objs(tb)?;
        Ok(Obj::InstSetStructObj(InstStructObj::new(name, args)))
    }

    pub fn atom(&self, tb: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SING {
            tb.skip()?;
            let right = tb.advance()?;
            if !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                tb.skip()?;
                let mut fields = vec![tb.advance()?.to_string()];
                while !tb.exceed_end_of_head() && tb.current()? == DOT_AKA_FIELD_ACCESS_SIGN {
                    tb.skip()?;
                    fields.push(tb.advance()?.to_string());
                }
                Ok(Atom::FieldAccessWithMod(FieldAccessWithMod::new(&left, &right, fields)))
            } else {
                Ok(Atom::IdentifierWithMod(IdentifierWithMod::new(&left, &right)))
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
                Ok(Atom::FieldAccess(FieldAccess::new(&left, fields)))
            } else {
                Ok(Atom::IdentifierAtom(Identifier::new(&left)))
            }
        }
    }

    pub fn identifier_or_identifier_with_mod(&self, tb: &mut TokenBlock) -> Result<IdentifierOrIdentifierWithMod, ParsingError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SING {
            tb.skip()?;
            let right = tb.advance()?;
            Ok(IdentifierOrIdentifierWithMod::IdentifierWithMod(IdentifierWithMod::new(&left, &right)))
        } else {
            Ok(IdentifierOrIdentifierWithMod::Identifier(Identifier::new(&left)))
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