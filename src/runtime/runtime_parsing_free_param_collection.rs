use crate::obj::DefStructFieldFreeParamObj;
use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone)]
pub struct FreeParamCollection {
    pub params: HashMap<String, Vec<FreeParamTypeAndLineFile>>,
}

#[derive(Clone, Debug)]
pub struct FreeParamTypeAndLineFile {
    pub kind: ParamObjType,
    pub binding: SymbolBinding,
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

    pub fn begin_scope(
        &mut self,
        kind: ParamObjType,
        bindings: &[SymbolBinding],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let mut names_in_new_scope: Vec<&str> = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let n = binding.name();
            let duplicates_new_name = names_in_new_scope.contains(&n);
            let duplicates_active_binding = self
                .params
                .get(n)
                .map(|stack| stack.iter().any(|binding| binding.kind == kind))
                .unwrap_or(false);
            if duplicates_new_name || duplicates_active_binding {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "free parameter `{}` is already bound as {:?} in an active scope",
                            n, kind
                        ),
                        line_file,
                    ),
                )));
            }
            names_in_new_scope.push(n);
        }
        for binding in bindings {
            let n = binding.name();
            self.params
                .entry(n.to_string())
                .or_default()
                .push(FreeParamTypeAndLineFile {
                    kind,
                    binding: binding.clone(),
                    line_file: line_file.clone(),
                });
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
        self.params
            .get(name)
            .map_or(false, |stack| !stack.is_empty())
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
            ParamObjType::Forall => ForallFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::DefHeader => DefHeaderFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::Exist => ExistFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::SetBuilder => SetBuilderFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::FnSet => FnSetFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::Induc => ByInducFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::DefAlgo => DefAlgoFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::DefStructField => {
                DefStructFieldFreeParamObj::new(top.binding.as_ref()).into()
            }
            ParamObjType::TupleIndex => TupleIndexFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::CartIndex => CartIndexFreeParamObj::new(top.binding.as_ref()).into(),
            ParamObjType::Identifier => {
                Identifier::new_bound(name.to_string(), top.binding.as_ref()).into()
            }
            ParamObjType::TheoremInstantiation
            | ParamObjType::AlphaRename
            | ParamObjType::BinderRetag(_) => unreachable!(
                "resolve_identifier_to_free_param_obj: instantiation modes are not parser scopes"
            ),
        }
    }
}
