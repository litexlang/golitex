use crate::keywords::{INFIX_FN_NAME_SIGN, MOD_SEPARATOR};
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::obj::{Obj, FnObj};
use crate::atom::{Atom, AtomWithoutModName, AtomWithModName};
use crate::errors::ParsingError;

impl Parser {
    pub fn obj(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        let left = self.obj_hierarchy0(token_block)?;
        match token_block.current_token() {
            Some(INFIX_FN_NAME_SIGN) => {
                let fn_name = self.atom(token_block)?;
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

    pub fn obj_hierarchy0(&self, token_block: &mut TokenBlock) -> Result<Obj, ParsingError> {
        panic!("Not implemented");
    }

    pub fn atom(&self, token_block: &mut TokenBlock) -> Result<Atom, ParsingError> {
        let left = token_block.advance()?;
        if token_block.current_token() == Some(MOD_SEPARATOR) {
            token_block.skip_without_checking();
            let right = token_block.advance()?;
            Ok(Atom::AtomWithModName(AtomWithModName::new(&left, &right)))
        } else {
            Ok(Atom::AtomWithoutModName(AtomWithoutModName::new(&left)))
        }
    }
}