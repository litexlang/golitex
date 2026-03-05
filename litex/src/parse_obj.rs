use crate::keywords::{
    ADD, CAP, CART, CHOOSE, CLOSED_RANGE, COLON, COMMA, COUNT, DISJOINT_UNION, DIV,
    INFIX_FN_NAME_SIGN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, INTERSECT,
    LEFT_BRACE, LEFT_BRACKET, LEFT_CURLY_BRACE, MOD, DOT, MUL, N, N_POS, POW,
    POWER_SET, PROJ, Q, Q_NEG, Q_NZ, Q_POS, R, RANGE, R_NEG, R_NZ, R_POS,
    RIGHT_BRACE, RIGHT_CURLY_BRACE, RIGHT_BRACKET, CART_DIM, SET_MINUS, SUB,
    UNION, VAL, Z, Z_NEG, Z_NZ, Z_POS, CUP, FN,
    is_key_symbol_or_keyword,
};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::obj::{
    Obj, FnObj, FnSetObj, FnSetWithDom, FnSetWithoutDom, Add, Mul, Div, Mod, Sub, Pow, Number, InstSetTemplateObj, ListSet,
    NPosObj, NObj, QObj, ZObj, RObj, QPos, ZPos, RPos, QNeg, ZNeg, RNeg, QNz, ZNz, RNz,
    ObjAtIndex, Union, Intersect, SetMinus, DisjointUnion, Cup, Cap, PowerSet, Choose,
    Cart, CartDim, Proj, Count, Range, ClosedRange, Val,
};
use crate::atom::{Atom, AtomWithoutModName, AtomWithModName};
use crate::errors::ParsingError;
use crate::parameter_type_and_property::ParamDefWithParamSet;

impl Parser {
    pub fn obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.obj_hierarchy0(tb)
    }

    fn obj_hierarchy0(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy1(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            INFIX_FN_NAME_SIGN => {
                let fn_name = self.atom(tb)?;
                
                let right = self.obj(tb)?;

                if is_key_symbol_or_keyword(&fn_name.to_string()) {
                    return match fn_name.to_string().as_str() {
                        UNION => Ok(Obj::Union(Union::new(left, right))),
                        INTERSECT => Ok(Obj::Intersect(Intersect::new(left, right))),
                        SET_MINUS => Ok(Obj::SetMinus(SetMinus::new(left, right))),
                        DISJOINT_UNION => Ok(Obj::DisjointUnion(DisjointUnion::new(left, right))),
                        RANGE => Ok(Obj::Range(Range::new(left, right))),
                        CLOSED_RANGE => Ok(Obj::ClosedRange(ClosedRange::new(left, right))),
                        PROJ => Ok(Obj::Proj(Proj::new(left, right))),
                        _ => Err(ParsingError::new(&format!("Invalid infix function name: {}", fn_name), tb.line_file_index)),
                    };
                }

                let head = match fn_name {
                    Atom::AtomWithoutModName(a) => Obj::AtomWithoutModName(a),
                    Atom::AtomWithModName(a) => Obj::AtomWithModName(a),
                };
                Ok(Obj::FnObj(FnObj::new(head, vec![left, right])))
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy1(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy2(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            MUL => {
                tb.skip()?;
                let right = self.obj_hierarchy2(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mul(Mul::new(left, right, false)))
                } else {
                    Ok(Obj::Mul(Mul::new(left, right, true)))
                }
            },
            DIV => {
                tb.skip()?;
                let right = self.obj_hierarchy2(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Div(Div::new(left, right, false)))
                } else {
                    Ok(Obj::Div(Div::new(left, right, true)))
                }
            },
            MOD => {
                tb.skip()?;
                let right = self.obj_hierarchy2(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mod(Mod::new(left, right, false)))
                } else {
                    Ok(Obj::Mod(Mod::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy2(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy3(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            ADD => {
                tb.skip()?;
                let right = self.obj_hierarchy3(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Add(Add::new(left, right, false)))
                } else {
                    Ok(Obj::Add(Add::new(left, right, true)))
                }
            },
            SUB => {
                tb.skip()?;
                let right = self.obj_hierarchy3(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Sub(Sub::new(left, right, false)))
                } else {
                    Ok(Obj::Sub(Sub::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy3(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy4(tb)?;
        if tb.exceed_end_of_head() {
            return Ok(left);
        }
        match tb.current_token_empty_if_exceed_end_of_head() {
            POW => {
                tb.skip()?;
                let right = self.obj_hierarchy4(tb)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Pow(Pow::new(left, right, false)))
                } else {
                    Ok(Obj::Pow(Pow::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

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

    fn obj_hierarchy5(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        match tb.current_token_empty_if_exceed_end_of_head() {
            LEFT_CURLY_BRACE => {
                self.set_builder_or_set_list(tb)
            },
            INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL => {
                self.instantiated_set_template_obj(tb)
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
            params_def_with_set.push(ParamDefWithParamSet::ParamAndItsSetPair(param, set));
            if tb.current()? == COLON {
                break;
            }
            tb.skip_token(COMMA)?;
        }
        tb.skip_token(COLON)?;
        let mut dom_facts = vec![self.or_and_spec_fact(tb)?];
        while tb.current()? == COMMA {
            tb.skip_token(COMMA)?;
            dom_facts.push(self.or_and_spec_fact(tb)?);
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

            if tb.current()? == DOT {
                tb.skip()?;
                let fraction = tb.advance()?;
                let number = format!("{}{}{}", number, DOT, fraction);
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
        let is_atom = matches!(result, Obj::AtomWithoutModName(_) | Obj::AtomWithModName(_));
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
        if tok == DISJOINT_UNION {
            tb.skip()?;
            let args = self.braced_objs(tb)?;
            if args.len() != 2 { return Err(ParsingError::new("disjoint_union expects 2 arguments", tb.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::DisjointUnion(DisjointUnion::new(it.next().unwrap(), it.next().unwrap())));
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
        match atom {
            Atom::AtomWithoutModName(a) => Ok(Obj::AtomWithoutModName(a)),
            Atom::AtomWithModName(a) => Ok(Obj::AtomWithModName(a)),
        }
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
        let left = self.obj(tb)?;
        if tb.current()? == COMMA {
            self.set_builder(tb, left)
        } else {
            self.set_list(tb, left)
        }
    }

    fn set_list(&self, tb: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        let mut objs = vec![left_most_obj];
        while tb.current()? != RIGHT_CURLY_BRACE {
            objs.push(self.obj(tb)?);
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(Obj::ListSet(ListSet::new(objs)))
    }

    fn set_builder(&self, tb: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        match left_most_obj {
            Obj::AtomWithoutModName(a) => {
                let param = a.name;
                let param_set = self.obj(tb)?;
                _ = param;
                _ = param_set;
                tb.skip_token(COLON)?;
                panic!("需要能parse fact")
            }
            _ => Err(ParsingError::new("Expected atom without mod name", tb.line_file_index))
        }
    }

    fn instantiated_set_template_obj(&self, tb: &mut TokenBlock) -> Result<Obj, ParsingError> {
        tb.skip_token(INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL)?;
        let name = self.atom(tb)?;
        let args = self.braced_objs(tb)?;
        Ok(Obj::InstSetTemplateObj(InstSetTemplateObj::new(name, args)))
    }

    pub fn atom(&self, tb: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == DOT {
            tb.skip()?;
            let right = tb.advance()?;
            Ok(Atom::AtomWithModName(AtomWithModName::new(&left, &right)))
        } else {
            Ok(Atom::AtomWithoutModName(AtomWithoutModName::new(&left)))
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