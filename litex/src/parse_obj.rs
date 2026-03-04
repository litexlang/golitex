use crate::keywords::{ADD, COMMA, COLON, DIV, INFIX_FN_NAME_SIGN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, LEFT_BRACE, LEFT_CURLY_BRACE, MOD, MOD_SEPARATOR, MUL, POW, RIGHT_BRACE, RIGHT_CURLY_BRACE, SUB, is_key_symbol_or_keyword};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::obj::{Obj, FnObj, Add, Mul, Div, Mod, Sub, Pow, Number, InstSetTemplateObj, ListSet};
use crate::atom::{Atom, AtomWithoutModName, AtomWithModName};
use crate::errors::ParsingError;

impl Parser {
    pub fn obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.obj_hierarchy0(token_block)
    }

    fn obj_hierarchy0(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy1(token_block)?;
        match token_block.current_token()? {
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
        match token_block.current_token()? {
            MUL => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mul(Mul::new(left, right, false)))
                } else {
                    Ok(Obj::Mul(Mul::new(left, right, true)))
                }
            },
            DIV => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Div(Div::new(left, right, false)))
                } else {
                    Ok(Obj::Div(Div::new(left, right, true)))
                }
            },
            MOD => {
                token_block.skip_without_checking()?;
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
        match token_block.current_token()? {
            ADD => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy3(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Add(Add::new(left, right, false)))
                } else {
                    Ok(Obj::Add(Add::new(left, right, true)))
                }
            },
            SUB => {
                token_block.skip_without_checking()?;
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
        match token_block.current_token()? {
            POW => {
                token_block.skip_without_checking()?;
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
        match token_block.current_token()? {
            LEFT_CURLY_BRACE => {
                self.set_builder_or_set_list(token_block)
            },
            INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL => {
                self.instantiated_set_template_obj(token_block)
            },
            _ => self.fn_obj_or_number_or_atom(token_block)
        }
    }

    fn fn_obj_or_number_or_atom(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let token = token_block.current_token()?;

        if starts_with_digit(token) {
            if is_number(token) {
                Ok(Obj::Number(Number::new(token)))
            } else {
                Err(ParsingError::new(&format!("Invalid number: {}", token), token_block.line_file_index))
            }
        } else {
            let left = self.atom(token_block)?;
            let mut result: Obj = match left {
                Atom::AtomWithoutModName(a) => Obj::AtomWithoutModName(a),
                Atom::AtomWithModName(a) => Obj::AtomWithModName(a),
            };
            while token_block.current_token()? == LEFT_BRACE {
                let args = self.braced_objs(token_block)?;
                result = Obj::FnObj(FnObj::new(result, args));
            }
            Ok(result)
        }
    }

    fn braced_objs(&self, token_block: &mut TokenBlock) -> Result<Vec<Obj>, ParsingError> {
        token_block.skip_token(LEFT_BRACE)?;
        let mut objs = vec![self.obj(token_block)?];
        while token_block.current_token()? == COMMA {
            token_block.skip_token(COMMA)?;
            objs.push(self.obj(token_block)?);
        }
        token_block.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    fn set_builder_or_set_list(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj(token_block)?;
        if token_block.current_token()? == COMMA {
            self.set_builder(token_block, left)
        } else {
            self.set_list(token_block, left)
        }
    }

    fn set_list(&self, token_block: &mut TokenBlock, left_most_obj: Obj) -> Result<Obj, ParsingError> {
        let mut objs = vec![left_most_obj];
        while token_block.current_token()? != RIGHT_CURLY_BRACE {
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
        if token_block.current_token()? == MOD_SEPARATOR {
            token_block.skip_without_checking()?;
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