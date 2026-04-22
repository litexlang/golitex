use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone)]
pub struct FreeParamCollection {
    pub params: HashMap<String, Vec<FreeParamTypeAndLineFile>>,
}

#[derive(Clone, Debug)]
pub struct FreeParamTypeAndLineFile {
    pub kind: ParamObjType,
    pub line_file: LineFile,
}

impl FreeParamCollection {
    pub fn new() -> Self {
        FreeParamCollection {
            params: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.params.clear();
    }

    fn push_param(
        &mut self,
        name: String,
        kind: ParamObjType,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let stack = self.params.entry(name.clone()).or_default();
        if stack.iter().any(|b| b.kind == kind) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "free parameter `{}` is already bound as {:?} in an active scope",
                        name, kind
                    ),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        stack.push(FreeParamTypeAndLineFile { kind, line_file });
        Ok(())
    }

    pub fn begin_scope(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for n in names {
            self.push_param(n.clone(), kind, line_file.clone())?;
        }
        Ok(())
    }

    pub fn end_scope(&mut self, kind: ParamObjType, names: &[String]) {
        for n in names {
            let Some(stack) = self.params.get_mut(n) else {
                panic!("free param stack missing for `{}` on end_scope", n);
            };
            let Some(top) = stack.pop() else {
                panic!("free param stack for `{}` empty on end_scope", n);
            };
            debug_assert_eq!(top.kind, kind);
            if stack.is_empty() {
                self.params.remove(n);
            }
        }
    }

    pub fn name_is_in_any_free_param_map(&self, name: &str) -> bool {
        self.params.get(name).map_or(false, |stack| !stack.is_empty())
    }

    pub fn resolve_identifier_to_free_param_obj(&self, name: &str) -> Obj {
        if !self.name_is_in_any_free_param_map(name) {
            return Identifier::new(name.to_string()).into();
        }
        let Some(stack) = self.params.get(name) else {
            return Identifier::new(name.to_string()).into();
        };
        let Some(top) = stack.last() else {
            return Identifier::new(name.to_string()).into();
        };
        match top.kind {
            ParamObjType::Forall => ForallFreeParamObj::new(name.to_string()).into(),
            ParamObjType::DefHeader => DefHeaderFreeParamObj::new(name.to_string()).into(),
            ParamObjType::Exist => ExistFreeParamObj::new(name.to_string()).into(),
            ParamObjType::SetBuilder => SetBuilderFreeParamObj::new(name.to_string()).into(),
            ParamObjType::FnSet => FnSetFreeParamObj::new(name.to_string()).into(),
            ParamObjType::Induc => ByInducFreeParamObj::new(name.to_string()).into(),
            ParamObjType::DefAlgo => DefAlgoFreeParamObj::new(name.to_string()).into(),
            ParamObjType::Identifier => Identifier::new(name.to_string()).into(),
        }
    }
}
