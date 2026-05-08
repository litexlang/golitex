use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByStructBinding {
    pub name: String,
    pub tuple: Obj,
    pub struct_ty: StructAsParamType,
}

#[derive(Clone)]
pub struct ByStructValueBinding {
    pub name: String,
    pub value: Obj,
}

#[derive(Clone)]
pub struct ByStructStmt {
    pub struct_bindings: Vec<ByStructBinding>,
    pub value_bindings: Vec<ByStructValueBinding>,
    pub forall_fact: ForallFact,
    pub line_file: LineFile,
}

impl ByStructBinding {
    pub fn new(name: String, tuple: Obj, struct_ty: StructAsParamType) -> Self {
        ByStructBinding {
            name,
            tuple,
            struct_ty,
        }
    }
}

impl ByStructValueBinding {
    pub fn new(name: String, value: Obj) -> Self {
        ByStructValueBinding { name, value }
    }
}

impl ByStructStmt {
    pub fn new(
        struct_bindings: Vec<ByStructBinding>,
        value_bindings: Vec<ByStructValueBinding>,
        forall_fact: ForallFact,
        line_file: LineFile,
    ) -> Self {
        ByStructStmt {
            struct_bindings,
            value_bindings,
            forall_fact,
            line_file,
        }
    }
}

impl fmt::Display for ByStructBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}",
            self.name, FROM, self.tuple, AS, self.struct_ty.name
        )?;
        if !self.struct_ty.args.is_empty() {
            write!(
                f,
                "{}{}{}",
                LEFT_BRACE,
                vec_to_string_join_by_comma(&self.struct_ty.args),
                RIGHT_BRACE
            )?;
        }
        Ok(())
    }
}

impl fmt::Display for ByStructValueBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.name, EQUAL, self.value)
    }
}

impl fmt::Display for ByStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();
        for binding in self.struct_bindings.iter() {
            parts.push(binding.to_string());
        }
        for binding in self.value_bindings.iter() {
            parts.push(binding.to_string());
        }
        write!(
            f,
            "{} {} {}{} {}",
            BY,
            STRUCT,
            vec_to_string_join_by_comma(&parts),
            COLON,
            self.forall_fact
        )
    }
}
