use crate::keywords::{
    ADD, CAP, CART, CHOICE, CLOSED_RANGE, COLON, COMMA, COUNT, DISJOINT_UNION, DIV,
    INFIX_FN_NAME_SIGN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, INTERSECT,
    LEFT_BRACE, LEFT_BRACKET, LEFT_CURLY_BRACE, MOD, DOT, MUL, N, N_POS, POW,
    POWER_SET, PROJ, Q, Q_NEG, Q_NZ, Q_POS, R, RANGE, R_NEG, R_NZ, R_POS,
    RIGHT_BRACE, RIGHT_CURLY_BRACE, RIGHT_BRACKET, SET_DIM, SET_MINUS, SUB,
    UNION, VAL, Z, Z_NEG, Z_NZ, Z_POS, CUP,
    is_key_symbol_or_keyword,
};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::obj::{
    Obj, FnObj, Add, Mul, Div, Mod, Sub, Pow, Number, InstSetTemplateObj, ListSet,
    NPosObj, NObj, QObj, ZObj, RObj, QPos, ZPos, RPos, QNeg, ZNeg, RNeg, QNz, ZNz, RNz,
    ObjAtIndex, Union, Intersect, SetMinus, DisjointUnion, Cup, Cap, PowerSet, Choose,
    Cart, SetDim, Proj, Count, Range, ClosedRange, Val,
};
use crate::atom::{Atom, AtomWithoutModName, AtomWithModName};
use crate::errors::ParsingError;

impl Parser {
    pub fn obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.obj_hierarchy0(token_block)
    }

    fn obj_hierarchy0(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy1(token_block)?;
        match token_block.current()? {
            INFIX_FN_NAME_SIGN => {
                let fn_name = self.atom(token_block)?;

                if is_key_symbol_or_keyword(&fn_name.to_string()) {
                    return Err(ParsingError::new(&format!("Invalid function name behind infix function name sign {}: {}", INFIX_FN_NAME_SIGN, fn_name), token_block.line_file_index));
                }
                
                let right = self.obj(token_block)?;
                let head = match fn_name {
                    Atom::AtomWithoutModName(a) => Obj::AtomWithoutModName(a),
                    Atom::AtomWithModName(a) => Obj::AtomWithModName(a),
                };
                Ok(Obj::FnObj(FnObj::new(head, vec![left, right])))
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy1(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy2(token_block)?;
        match token_block.current()? {
            MUL => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mul(Mul::new(left, right, false)))
                } else {
                    Ok(Obj::Mul(Mul::new(left, right, true)))
                }
            },
            DIV => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Div(Div::new(left, right, false)))
                } else {
                    Ok(Obj::Div(Div::new(left, right, true)))
                }
            },
            MOD => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mod(Mod::new(left, right, false)))
                } else {
                    Ok(Obj::Mod(Mod::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy2(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy3(token_block)?;
        match token_block.current()? {
            ADD => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy3(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Add(Add::new(left, right, false)))
                } else {
                    Ok(Obj::Add(Add::new(left, right, true)))
                }
            },
            SUB => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy3(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Sub(Sub::new(left, right, false)))
                } else {
                    Ok(Obj::Sub(Sub::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy3(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy4(token_block)?;
        match token_block.current()? {
            POW => {
                token_block.no_check_skip()?;
                let right = self.obj_hierarchy4(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Pow(Pow::new(left, right, false)))
                } else {
                    Ok(Obj::Pow(Pow::new(left, right, true)))
                }
            },
            _ => Ok(left),
        }
    }

    fn obj_hierarchy4(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy5(token_block)?;
        match token_block.current()? {
            LEFT_BRACKET => {
                token_block.skip_token(LEFT_BRACKET)?;
                let obj = self.obj(token_block)?;
                token_block.skip_token(RIGHT_BRACKET)?;
                Ok(Obj::ObjAtIndex(ObjAtIndex::new(left, obj)))
            }
            _ => Ok(left),
        }
    }

    fn obj_hierarchy5(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        match token_block.current()? {
            LEFT_CURLY_BRACE => {
                self.set_builder_or_set_list(token_block)
            },
            INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL => {
                self.instantiated_set_template_obj(token_block)
            },
            _ => self.fn_obj_or_number_or_atom(token_block)
        }
    }

    /// 解析「主元」：数字、单符号集合(N/Q/...)、多元关键字(union/intersect/...)、或普通 atom。
    /// 若得到 atom，调用方再给其接若干 (args) 变成 FnObj。
    fn fn_obj_or_number_or_atom(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let token = token_block.current()?;

        // 0. (...)
        if token == LEFT_BRACE {
            token_block.no_check_skip()?;
            let obj = self.obj(token_block)?;
            token_block.skip_token(RIGHT_BRACE)?;
            return Ok(obj);
        }

        // 1. 数字
        if starts_with_digit(token) {
            let number = token_block.advance()?;
            if token_block.current()? != DOT {
                token_block.no_check_skip()?;
                let fraction = token_block.advance()?;
                let number = format!("{}{}{}", number, DOT, fraction);
                if !is_number(&number) {
                    return Err(ParsingError::new(&format!("Invalid number: {}", number), token_block.line_file_index));
                }
                return Ok(Obj::Number(Number::new(&number)));
            } else {
                if !is_number(&number) {
                    return Err(ParsingError::new(&format!("Invalid number: {}", number), token_block.line_file_index));
                }
                return Ok(Obj::Number(Number::new(&number)));
            }
        }

        // 2. 单符号集合、多元关键字、或 atom
        let mut result = self.parse_primary_obj(token_block)?;

        // 3. 若是 atom，后面可以接多组 (args)，每组变成 FnObj(head, args)
        let is_atom = matches!(result, Obj::AtomWithoutModName(_) | Obj::AtomWithModName(_));
        if is_atom {
            while token_block.current()? == LEFT_BRACE {
                let args = self.braced_objs(token_block)?;
                result = Obj::FnObj(FnObj::new(result, args));
            }
        }
        Ok(result)
    }

    /// 解析「主元」：当前 token 必须是单符号集合名、多元关键字、或普通标识符(atom)。
    fn parse_primary_obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let tok = token_block.current()?;

        // 单符号集合（无参）
        if tok == N_POS { token_block.no_check_skip()?; return Ok(Obj::NPosObj(NPosObj::new())); }
        if tok == N { token_block.no_check_skip()?; return Ok(Obj::NObj(NObj::new())); }
        if tok == Q { token_block.no_check_skip()?; return Ok(Obj::QObj(QObj::new())); }
        if tok == Z { token_block.no_check_skip()?; return Ok(Obj::ZObj(ZObj::new())); }
        if tok == R { token_block.no_check_skip()?; return Ok(Obj::RObj(RObj::new())); }
        if tok == Q_POS { token_block.no_check_skip()?; return Ok(Obj::QPos(QPos::new())); }
        if tok == Z_POS { token_block.no_check_skip()?; return Ok(Obj::ZPos(ZPos::new())); }
        if tok == R_POS { token_block.no_check_skip()?; return Ok(Obj::RPos(RPos::new())); }
        if tok == Q_NEG { token_block.no_check_skip()?; return Ok(Obj::QNeg(QNeg::new())); }
        if tok == Z_NEG { token_block.no_check_skip()?; return Ok(Obj::ZNeg(ZNeg::new())); }
        if tok == R_NEG { token_block.no_check_skip()?; return Ok(Obj::RNeg(RNeg::new())); }
        if tok == Q_NZ { token_block.no_check_skip()?; return Ok(Obj::QNz(QNz::new())); }
        if tok == Z_NZ { token_block.no_check_skip()?; return Ok(Obj::ZNz(ZNz::new())); }
        if tok == R_NZ { token_block.no_check_skip()?; return Ok(Obj::RNz(RNz::new())); }

        // 多元关键字：吃关键字 + 括号里若干 obj
        if tok == UNION {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("union expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Union(Union::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == INTERSECT {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("intersect expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Intersect(Intersect::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == SET_MINUS {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("set_minus expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::SetMinus(SetMinus::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == DISJOINT_UNION {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("disjoint_union expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::DisjointUnion(DisjointUnion::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == CAP {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("cap expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Cap(Cap::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == CHOICE {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("choice expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Choose(Choose::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == PROJ {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("proj expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Proj(Proj::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == RANGE {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("range expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::Range(Range::new(it.next().unwrap(), it.next().unwrap())));
        }
        if tok == CLOSED_RANGE {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 2 { return Err(ParsingError::new("closed_range expects 2 arguments", token_block.line_file_index)); }
            let mut it = args.into_iter();
            return Ok(Obj::ClosedRange(ClosedRange::new(it.next().unwrap(), it.next().unwrap())));
        }

        if tok == CUP {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 1 { return Err(ParsingError::new("cup expects 1 argument", token_block.line_file_index)); }
            return Ok(Obj::Cup(Cup::new(args.into_iter().next().unwrap())));
        }
        if tok == POWER_SET {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 1 { return Err(ParsingError::new("power_set expects 1 argument", token_block.line_file_index)); }
            return Ok(Obj::PowerSet(PowerSet::new(args.into_iter().next().unwrap())));
        }
        if tok == SET_DIM {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 1 { return Err(ParsingError::new("set_dim expects 1 argument", token_block.line_file_index)); }
            return Ok(Obj::SetDim(SetDim::new(args.into_iter().next().unwrap())));
        }
        if tok == COUNT {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 1 { return Err(ParsingError::new("count expects 1 argument", token_block.line_file_index)); }
            return Ok(Obj::Count(Count::new(args.into_iter().next().unwrap())));
        }
        if tok == VAL {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            if args.len() != 1 { return Err(ParsingError::new("val expects 1 argument", token_block.line_file_index)); }
            return Ok(Obj::Val(Val::new(args.into_iter().next().unwrap())));
        }

        if tok == CART {
            token_block.no_check_skip()?;
            let args = self.braced_objs(token_block)?;
            return Ok(Obj::Cart(Cart::new(args)));
        }

        // 普通 atom（标识符）
        let atom = self.atom(token_block)?;
        match atom {
            Atom::AtomWithoutModName(a) => Ok(Obj::AtomWithoutModName(a)),
            Atom::AtomWithModName(a) => Ok(Obj::AtomWithModName(a)),
        }
    }

    fn braced_objs(&self, token_block: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        token_block.skip_token(LEFT_BRACE)?;
        let mut objs = vec![self.obj(token_block)?];
        while token_block.current()? == COMMA {
            token_block.skip_token(COMMA)?;
            objs.push(self.obj(token_block)?);
        }
        token_block.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    fn set_builder_or_set_list(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj(token_block)?;
        if token_block.current()? == COMMA {
            self.set_builder(token_block, left)
        } else {
            self.set_list(token_block, left)
        }
    }

    fn set_list(&self, token_block: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        let mut objs = vec![left_most_obj];
        while token_block.current()? != RIGHT_CURLY_BRACE {
            let obj = self.obj(token_block)?;
            objs.push(obj);
        }
        token_block.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(Obj::ListSet(ListSet::new(objs)))
    }

    fn set_builder(&self, token_block: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        match left_most_obj {
            Obj::AtomWithoutModName(a) => {
                let param = a.name;
                let param_set = self.obj(token_block)?;
                _ = param;
                _ = param_set;
                token_block.skip_token(COLON)?;
                panic!("需要能parse fact")
            }
            _ => Err(ParsingError::new("Expected atom without mod name", token_block.line_file_index))
        }
    }

    fn instantiated_set_template_obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        token_block.skip_token(INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL)?;
        let name = self.atom(token_block)?;
        let args = self.braced_objs(token_block)?;
        Ok(Obj::InstSetTemplateObj(InstSetTemplateObj::new(name, args)))
    }

    pub fn atom(&self, token_block: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = token_block.advance()?;
        if token_block.current()? == DOT {
            token_block.no_check_skip()?;
            let right = token_block.advance()?;
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