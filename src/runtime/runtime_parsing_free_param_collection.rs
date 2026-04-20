use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FreeParamObjType {
    Forall,
    Def,
    Exist,
    SetBuilder,
    FnSet,
}

#[derive(Clone, Debug)]
pub struct FreeParamScopeFrame {
    pub kind: FreeParamObjType,
    pub names: Vec<String>,
}

pub struct FreeParamCollection {
    pub forall_free_params: HashMap<String, LineFile>,
    pub def_free_param: HashMap<String, LineFile>,
    pub exist_free_params: HashMap<String, LineFile>,
    pub set_builder_free_params: HashMap<String, LineFile>,
    pub fn_set_free_params: HashMap<String, LineFile>,
    pub free_param_scope_stack: Vec<FreeParamScopeFrame>,
}

impl FreeParamCollection {
    pub fn new() -> Self {
        FreeParamCollection {
            forall_free_params: HashMap::new(),
            def_free_param: HashMap::new(),
            exist_free_params: HashMap::new(),
            set_builder_free_params: HashMap::new(),
            fn_set_free_params: HashMap::new(),
            free_param_scope_stack: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.forall_free_params.clear();
        self.def_free_param.clear();
        self.exist_free_params.clear();
        self.set_builder_free_params.clear();
        self.fn_set_free_params.clear();
        self.free_param_scope_stack.clear();
    }

    pub fn begin_scope(
        &mut self,
        kind: FreeParamObjType,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for n in names {
            match kind {
                FreeParamObjType::Forall => {
                    self.put_forall_free_param(n.clone(), line_file.clone())?
                }
                FreeParamObjType::Def => self.put_def_free_param(n.clone(), line_file.clone())?,
                FreeParamObjType::Exist => {
                    self.put_exist_free_param(n.clone(), line_file.clone())?
                }
                FreeParamObjType::SetBuilder => {
                    self.put_set_builder_free_param(n.clone(), line_file.clone())?
                }
                FreeParamObjType::FnSet => {
                    self.put_fn_set_free_param(n.clone(), line_file.clone())?
                }
            }
        }
        self.free_param_scope_stack.push(FreeParamScopeFrame {
            kind,
            names: names.to_vec(),
        });
        Ok(())
    }

    pub fn end_scope(&mut self) {
        let Some(frame) = self.free_param_scope_stack.pop() else {
            return;
        };
        for n in &frame.names {
            match frame.kind {
                FreeParamObjType::Forall => {
                    self.forall_free_params.remove(n);
                }
                FreeParamObjType::Def => {
                    self.def_free_param.remove(n);
                }
                FreeParamObjType::Exist => {
                    self.exist_free_params.remove(n);
                }
                FreeParamObjType::SetBuilder => {
                    self.set_builder_free_params.remove(n);
                }
                FreeParamObjType::FnSet => {
                    self.fn_set_free_params.remove(n);
                }
            }
        }
    }

    pub fn name_is_in_any_free_param_map(&self, name: &str) -> bool {
        self.forall_free_params.contains_key(name)
            || self.def_free_param.contains_key(name)
            || self.exist_free_params.contains_key(name)
            || self.set_builder_free_params.contains_key(name)
            || self.fn_set_free_params.contains_key(name)
    }

    pub fn resolve_identifier_to_free_param_obj(&self, name: &str) -> Obj {
        if !self.name_is_in_any_free_param_map(name) {
            return Identifier::new(name.to_string()).into();
        }
        for frame in self.free_param_scope_stack.iter().rev() {
            let in_map = match frame.kind {
                FreeParamObjType::Forall => self.forall_free_params.contains_key(name),
                FreeParamObjType::Def => self.def_free_param.contains_key(name),
                FreeParamObjType::Exist => self.exist_free_params.contains_key(name),
                FreeParamObjType::SetBuilder => self.set_builder_free_params.contains_key(name),
                FreeParamObjType::FnSet => self.fn_set_free_params.contains_key(name),
            };
            if in_map {
                return match frame.kind {
                    FreeParamObjType::Forall => ForallFreeParamObj::new(name.to_string()).into(),
                    FreeParamObjType::Def => DefFreeParamObj::new(name.to_string()).into(),
                    FreeParamObjType::Exist => ExistFreeParamObj::new(name.to_string()).into(),
                    FreeParamObjType::SetBuilder => {
                        SetBuilderFreeParamObj::new(name.to_string()).into()
                    }
                    FreeParamObjType::FnSet => FnSetFreeParamObj::new(name.to_string()).into(),
                };
            }
        }
        panic!(
            "free parameter `{}` is registered in a map but not resolved by the binder stack",
            name
        );
    }

    pub fn resolve_field_access_to_free_param_obj(
        &self,
        name: &str,
        field: &str,
    ) -> Result<Obj, RuntimeError> {
        if !self.name_is_in_any_free_param_map(name) {
            return Ok(FieldAccess::new(name.to_string(), field.to_string()).into());
        }
        for frame in self.free_param_scope_stack.iter().rev() {
            let in_map = match frame.kind {
                FreeParamObjType::Forall => self.forall_free_params.contains_key(name),
                FreeParamObjType::Def => self.def_free_param.contains_key(name),
                FreeParamObjType::Exist => self.exist_free_params.contains_key(name),
                FreeParamObjType::SetBuilder => self.set_builder_free_params.contains_key(name),
                FreeParamObjType::FnSet => self.fn_set_free_params.contains_key(name),
            };
            if in_map {
                return match frame.kind {
                    FreeParamObjType::Forall => Ok(ForallFreeParamFieldAccess::new(
                        name.to_string(),
                        field.to_string(),
                    )
                    .into()),
                    FreeParamObjType::Def
                    | FreeParamObjType::Exist
                    | FreeParamObjType::SetBuilder
                    | FreeParamObjType::FnSet => Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            format!(
                                "field access `{}` on {:?} free parameter `{}` is not supported",
                                field, frame.kind, name
                            ),
                            default_line_file(),
                            None,
                            vec![],
                        ),
                    ))),
                };
            }
        }
        panic!(
            "free parameter `{}` (field `{}`) is registered but not resolved by the binder stack",
            name, field
        );
    }

    pub fn put_forall_free_param(
        &mut self,
        free_param: String,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.forall_free_params.contains_key(&free_param) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "forall free parameter `{}` is already bound in this collection",
                        free_param
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        self.forall_free_params.insert(free_param, line_file);
        Ok(())
    }

    pub fn put_def_free_param(
        &mut self,
        name: String,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.def_free_param.contains_key(&name) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "def free parameter `{}` is already bound in this collection",
                        name
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        self.def_free_param.insert(name, line_file);
        Ok(())
    }

    pub fn put_exist_free_param(
        &mut self,
        name: String,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.exist_free_params.contains_key(&name) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "exist free parameter `{}` is already bound in this collection",
                        name
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        self.exist_free_params.insert(name, line_file);
        Ok(())
    }

    pub fn put_set_builder_free_param(
        &mut self,
        name: String,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.set_builder_free_params.contains_key(&name) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "set builder free parameter `{}` is already bound in this collection",
                        name
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        self.set_builder_free_params.insert(name, line_file);
        Ok(())
    }

    pub fn put_fn_set_free_param(
        &mut self,
        name: String,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if self.fn_set_free_params.contains_key(&name) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "fn set free parameter `{}` is already bound in this collection",
                        name
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        self.fn_set_free_params.insert(name, line_file);
        Ok(())
    }
}
