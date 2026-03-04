use crate::keywords::{ADD, DIV, INFIX_FN_NAME_SIGN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, LEFT_CURLY_BRACE, MOD, MOD_SEPARATOR, MUL, POW, SUB, is_key_symbol_or_keyword};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::obj::{Obj, FnObj, Add, Mul, Div, Mod, Sub, Pow};
use crate::atom::{Atom, AtomWithoutModName, AtomWithModName};
use crate::errors::ParsingError;

impl Parser {
    pub fn obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        self.obj_hierarchy0(token_block)
    }

    fn obj_hierarchy0(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy1(token_block)?;
        match token_block.current_token() {
            Some(INFIX_FN_NAME_SIGN) => {
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
        match token_block.current_token() {
            Some(MUL) => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Mul(Mul::new(left, right, false)))
                } else {
                    Ok(Obj::Mul(Mul::new(left, right, true)))
                }
            },
            Some(DIV) => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy2(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Div(Div::new(left, right, false)))
                } else {
                    Ok(Obj::Div(Div::new(left, right, true)))
                }
            },
            Some(MOD) => {
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
        match token_block.current_token() {
            Some(ADD) => {
                token_block.skip_without_checking()?;
                let right = self.obj_hierarchy3(token_block)?;
                if !left.is_add_sub_mul_div_mod_pow() || !right.is_add_sub_mul_div_mod_pow() {
                    Ok(Obj::Add(Add::new(left, right, false)))
                } else {
                    Ok(Obj::Add(Add::new(left, right, true)))
                }
            },
            Some(SUB) => {
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
        match token_block.current_token() {
            Some(POW) => {
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
        match token_block.current_token() {
            Some(LEFT_CURLY_BRACE) => {
                self.set_builder_or_set_list(token_block)
            },
            Some(INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL) => {
                self.instantiated_set_template_obj(token_block)
            },
            _ => self.fn_obj_or_number_or_atom(token_block)
        }
    }

    fn fn_obj_or_number_or_atom(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        panic!("Not implemented");
    }

    fn set_builder_or_set_list(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        panic!("Not implemented");
    }

    fn instantiated_set_template_obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        panic!("Not implemented");
    }

    pub fn atom(&self, token_block: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = token_block.advance()?;
        if token_block.current_token() == Some(MOD_SEPARATOR) {
            token_block.skip_without_checking()?;
            let right = token_block.advance()?;
            Ok(Atom::AtomWithModName(AtomWithModName::new(&left, &right)))
        } else {
            Ok(Atom::AtomWithoutModName(AtomWithoutModName::new(&left)))
        }
    }
}