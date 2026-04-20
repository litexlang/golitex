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
    // Not for `begin_scope`; only for `inst_*` when any free-param kind may substitute.
    Full,
}

impl FreeParamObjType {
    pub fn subst_forall_free_param(self) -> bool {
        matches!(self, Self::Forall | Self::Full)
    }

    pub fn subst_def_free_param(self) -> bool {
        matches!(self, Self::Def | Self::Full)
    }

    pub fn subst_exist_free_param(self) -> bool {
        matches!(self, Self::Exist | Self::Full)
    }

    pub fn subst_set_builder_free_param(self) -> bool {
        matches!(self, Self::SetBuilder | Self::Full)
    }

    pub fn subst_fn_set_free_param(self) -> bool {
        matches!(self, Self::FnSet | Self::Full)
    }

    pub fn subst_struct_self_field_free_param(self) -> bool {
        matches!(self, Self::StructSelf | Self::Full)
    }

    pub fn subst_induc_free_param(self) -> bool {
        matches!(self, Self::Induc | Self::Full)
    }
}

#[derive(Clone, Debug)]
pub struct FreeParamBinding {
    pub kind: FreeParamObjType,
    pub line_file: LineFile,
}

pub struct FreeParamCollection {
    pub params: HashMap<String, Vec<FreeParamBinding>>,
    struct_self_depth: usize,
}

impl FreeParamCollection {
    pub fn new() -> Self {
        FreeParamCollection {
            params: HashMap::new(),
            struct_self_depth: 0,
        }
    }

    pub fn clear(&mut self) {
        self.params.clear();
        self.struct_self_depth = 0;
    }

    pub fn in_struct_self_scope(&self) -> bool {
        self.struct_self_depth > 0
    }

    fn push_binding(
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
        stack.push(FreeParamBinding { kind, line_file });
        Ok(())
    }

    pub fn begin_scope(
        &mut self,
        kind: FreeParamObjType,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if kind == FreeParamObjType::Full {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "`Full` is not a parsing scope kind for `begin_scope`".to_string(),
                    line_file,
                    None,
                    vec![],
                ),
            )));
        }
        for n in names {
            self.push_binding(n.clone(), kind, line_file.clone())?;
        }
        if kind == FreeParamObjType::StructSelf {
            self.struct_self_depth += 1;
        }
        Ok(())
    }

    pub fn end_scope(&mut self, kind: FreeParamObjType, names: &[String]) {
        if kind == FreeParamObjType::Full {
            return;
        }
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
        if kind == FreeParamObjType::StructSelf {
            self.struct_self_depth = self.struct_self_depth.saturating_sub(1);
        }
    }

    pub fn name_is_in_any_free_param_map(&self, name: &str) -> bool {
        self.params.get(name).map_or(false, |stack| {
            stack
                .iter()
                .any(|b| b.kind != FreeParamObjType::StructSelf)
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
            FreeParamObjType::Full => {
                panic!("Full must not appear on the parsing free-param scope stack")
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
            let msg = if self.in_struct_self_scope() {
                format!("unknown struct field `{}` in `self.{}`", field, field)
            } else {
                "`self.<field>` is only allowed in struct `<=>:` facts (and `<field>` must be a field name)"
                    .to_string()
            };
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
            FreeParamObjType::Forall => Ok(ForallFreeParamFieldAccess::new(
                name.to_string(),
                field.to_string(),
            )
            .into()),
            FreeParamObjType::Def
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
            FreeParamObjType::Full => {
                panic!("Full must not appear on the parsing free-param scope stack")
            }
        }
    }
}
