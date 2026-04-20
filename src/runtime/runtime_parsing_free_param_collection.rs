use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FreeParamObjType {
    Forall,
    Def,
    Exist,
    SetBuilder,
    FnSet,
    StructSelf,
    Induc,
    DefAlgo,
    Identifier,
}

/// Which free-parameter kind is being instantiated; map values carry concrete `Obj` types.
pub type InstObjState = FreeParamObjType;

#[derive(Clone, Debug)]
pub struct FreeParamTypeAndLineFile {
    pub kind: FreeParamObjType,
    pub line_file: LineFile,
}

pub struct FreeParamCollection {
    pub params: HashMap<String, Vec<FreeParamTypeAndLineFile>>,
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
        kind: FreeParamObjType,
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
        kind: FreeParamObjType,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if kind == FreeParamObjType::Identifier {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "`Identifier` is not a parsing scope kind for `begin_scope`".to_string(),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        for n in names {
            self.push_param(n.clone(), kind, line_file.clone())?;
        }
        Ok(())
    }

    pub fn end_scope(&mut self, kind: FreeParamObjType, names: &[String]) {
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
        self.params.get(name).map_or(false, |stack| {
            stack.iter().any(|b| b.kind != FreeParamObjType::StructSelf)
        })
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
            FreeParamObjType::Forall => ForallFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::Def => DefFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::Exist => ExistFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::SetBuilder => SetBuilderFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::FnSet => FnSetFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::StructSelf => {
                panic!("StructSelf scope does not bind identifier-shaped free parameters")
            }
            FreeParamObjType::Induc => ByInducFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::DefAlgo => DefAlgoFreeParamObj::new(name.to_string()).into(),
            FreeParamObjType::Identifier => {
                panic!("Identifier must not appear on the parsing free-param scope stack")
            }
        }
    }

    pub fn resolve_field_access_to_free_param_obj(
        &self,
        name: &str,
        field: &str,
    ) -> Result<Obj, RuntimeError> {
        if name == SELF {
            if let Some(stack) = self.params.get(field) {
                if let Some(top) = stack.last() {
                    if top.kind == FreeParamObjType::StructSelf {
                        return Ok(StructSelfFieldFreeParamObj::new(field.to_string()).into());
                    }
                }
            }
            let msg = format!(
                "`self.{0}`: `{0}` is not a struct field name bound in the current struct `<=>:` scope",
                field
            );
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(None, msg, default_line_file(), None, vec![]),
            )));
        }
        if !self.name_is_in_any_free_param_map(name) {
            return Ok(FieldAccess::new(name.to_string(), field.to_string()).into());
        }
        let Some(stack) = self.params.get(name) else {
            return Ok(FieldAccess::new(name.to_string(), field.to_string()).into());
        };
        let Some(top) = stack.last() else {
            return Ok(FieldAccess::new(name.to_string(), field.to_string()).into());
        };
        match top.kind {
            FreeParamObjType::Forall => {
                Ok(ForallFreeParamFieldAccess::new(name.to_string(), field.to_string()).into())
            }
            FreeParamObjType::Def
            | FreeParamObjType::DefAlgo
            | FreeParamObjType::Exist
            | FreeParamObjType::SetBuilder
            | FreeParamObjType::FnSet
            | FreeParamObjType::Induc => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    format!(
                        "field access `{}` on {:?} free parameter `{}` is not supported",
                        field, top.kind, name
                    ),
                    default_line_file(),
                    None,
                    vec![],
                ),
            ))),
            FreeParamObjType::StructSelf => {
                panic!("StructSelf scope does not use identifier-shaped field-access free params")
            }
            FreeParamObjType::Identifier => {
                panic!("Identifier must not appear on the parsing free-param scope stack")
            }
        }
    }
}
