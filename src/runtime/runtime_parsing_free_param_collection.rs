use crate::prelude::*;
use std::collections::HashMap;

pub struct FreeParamCollection {
    pub forall_free_params: HashMap<String, LineFile>,
    pub def_free_params: HashMap<String, LineFile>,
    pub exist_free_params: HashMap<String, LineFile>,
    pub set_builder_free_params: HashMap<String, LineFile>,
    pub fn_set_free_params: HashMap<String, LineFile>,
}

impl FreeParamCollection {
    pub fn new() -> Self {
        FreeParamCollection {
            forall_free_params: HashMap::new(),
            def_free_params: HashMap::new(),
            exist_free_params: HashMap::new(),
            set_builder_free_params: HashMap::new(),
            fn_set_free_params: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.forall_free_params.clear();
        self.def_free_params.clear();
        self.exist_free_params.clear();
        self.set_builder_free_params.clear();
        self.fn_set_free_params.clear();
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
        if self.def_free_params.contains_key(&name) {
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
        self.def_free_params.insert(name, line_file);
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
