//! Param-type struct：参数/字段上的类型绑定。
//!
//! ## `String` 与 [`FieldAccess`] 两套入口
//!
//! - [`Runtime::define_param_binding_for_param_type`]（[`exec_def_stmt`](crate::execute::exec_def_stmt)）里，
//!   普通参数名是 `&str`，事实里主体用 [`Obj::Identifier`]。
//! - 本文件中的 [`Runtime::define_param_binding_for_param_type_on_field_access`] 用于 **`param.field` 形态**：
//!   事实主体必须是 [`Obj::FieldAccess`]，例如 `g.id ∈ S` 而不是 `id ∈ S`。
//!
//! ## 示例
//!
//! ```text
//! struct group(R) { id: R, add: ... }
//! let g struct group(S):
//! ```
//!
//! 在登记 `defined_field_access_name["g"]` 之后，对 `id`、`add` 要分别建立与字段 [`ParamType`] 一致的事实，
//! 左端为 `FieldAccess { name: "g", fields: ["id"] }` 对应的 [`Obj::FieldAccess`]。

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// 与 [`define_param_binding_for_param_type`](crate::execute::exec_def_stmt) 类似，但**约束左端为 field access**。
    ///
    /// - `field_access`：已解析好的访问路径，如 `g.id` → [`FieldAccess::new`] `("g", ["id"])`。
    /// - `param_type`：该位置上应当满足的类型（可与定义中字段类型经 `instantiate` 后一致）。
    ///
    /// 嵌套 [`ParamType::Struct`] 时会在 [`Environment::defined_field_access_name`] 中以
    /// `field_access` 的字符串形式（[`FieldAccess`] 的 [`Display`]）为键登记子实例，并递归绑定子字段。
    pub(crate) fn define_param_binding_for_param_type_on_field_access(
        &mut self,
        field_access: &FieldAccess,
        param_type: &ParamType,
    ) -> Result<InferResult, RuntimeError> {
        let subject = obj_from_field_access(field_access);
        match param_type {
            ParamType::Family(family_ty) => {
                self.define_param_binding_family_on_obj(subject, family_ty)
            }
            ParamType::Obj(obj) => self.define_param_binding_obj_on_obj(subject, obj),
            ParamType::Set(set) => self.define_param_binding_set_on_obj(subject, set),
            ParamType::NonemptySet(nonempty_set) => {
                self.define_param_binding_nonempty_set_on_obj(subject, nonempty_set)
            }
            ParamType::FiniteSet(finite_set) => {
                self.define_param_binding_finite_set_on_obj(subject, finite_set)
            }
            ParamType::Struct(struct_ty) => {
                self.define_param_binding_struct_at_field_access(field_access, struct_ty)
            }
        }
    }

    pub(crate) fn define_param_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_param_type_struct_definition_by_name(&struct_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!(
                        "struct `{}` is not defined (needed for param `{}` of type `struct {}(...)`)",
                        struct_name, name, struct_name
                    ),
                    DEFAULT_LINE_FILE.clone(),
                    None,
                    None,
                )));
            }
        };

        let expected_count = ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if struct_ty.params.len() != expected_count {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "struct `{}` expects {} type argument(s) in `struct {}(...)`, got {}",
                    struct_name,
                    expected_count,
                    struct_name,
                    struct_ty.params.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
                None,
            )));
        }

        let inst = InstStructObj::new(struct_ty.name.clone(), struct_ty.params.clone());
        self.register_param_as_struct_instance(name, inst);

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &struct_ty.params,
        );

        self.bind_struct_fields_for_root_param(&def, &param_to_arg_map, name)
    }

    /// 根参数 `name`（如 `g`）已登记为 [`InstStructObj`] 后，对定义中每个字段做 field-access 上的类型绑定。
    fn bind_struct_fields_for_root_param(
        &mut self,
        def: &DefParamTypeStructStmt,
        param_to_arg_map: &HashMap<String, Obj>,
        root_param_name: &str,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for (field_name, field_param_type) in def.fields.iter() {
            let instantiated = field_param_type.instantiate(param_to_arg_map);
            let fa = FieldAccess::new(root_param_name.to_string(), vec![field_name.clone()]);
            let fr = self.define_param_binding_for_param_type_on_field_access(&fa, &instantiated)?;
            infer_result.new_infer_result_inside(fr);
        }
        Ok(infer_result)
    }

    /// 某 **field access 路径** 已视为 `struct_ty` 的实例（与根上 [`define_param_binding_struct`] 同构），
    /// 登记 `field_access.to_string()` → [`InstStructObj`]，并绑定该 struct 定义中的各字段。
    fn define_param_binding_struct_at_field_access(
        &mut self,
        field_access: &FieldAccess,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_param_type_struct_definition_by_name(&struct_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!(
                        "struct `{}` is not defined (needed for field `{}` of type `struct {}(...)`)",
                        struct_name,
                        field_access,
                        struct_name
                    ),
                    DEFAULT_LINE_FILE.clone(),
                    None,
                    None,
                )));
            }
        };

        let expected_count = ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if struct_ty.params.len() != expected_count {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "struct `{}` expects {} type argument(s), got {}",
                    struct_name,
                    expected_count,
                    struct_ty.params.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
                None,
            )));
        }

        let inst = InstStructObj::new(struct_ty.name.clone(), struct_ty.params.clone());
        self.register_param_as_struct_instance(&field_access.to_string(), inst);

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &struct_ty.params,
        );

        let mut infer_result = InferResult::new();
        for (field_name, field_param_type) in def.fields.iter() {
            let instantiated = field_param_type.instantiate(&param_to_arg_map);
            let fa = append_field_to_field_access(field_access, field_name);
            let fr = self.define_param_binding_for_param_type_on_field_access(&fa, &instantiated)?;
            infer_result.new_infer_result_inside(fr);
        }
        Ok(infer_result)
    }

    fn register_param_as_struct_instance(&mut self, env_key: &str, inst: InstStructObj) {
        self.top_level_env()
            .defined_field_access_name
            .insert(env_key.to_string(), inst);
    }

    fn define_param_binding_family_on_obj(
        &mut self,
        subject: Obj,
        family_ty: &FamilyParamType,
    ) -> Result<InferResult, RuntimeError> {
        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!("family `{}` is not defined", family_name),
                    DEFAULT_LINE_FILE.clone(),
                    None,
                    None,
                )));
            }
        };
        let expected_count = ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if family_ty.params.len() != expected_count {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "family `{}` expects {} type argument(s), got {}",
                    family_name,
                    expected_count,
                    family_ty.params.len()
                ),
                DEFAULT_LINE_FILE.clone(),
                None,
                None,
            )));
        }
        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_ty.params,
        );
        let member_set = def.equal_to.instantiate(&param_to_arg_map);
        let type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            subject,
            member_set,
            DEFAULT_LINE_FILE.clone(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_param_binding_obj_on_obj(
        &mut self,
        subject: Obj,
        obj: &Obj,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            subject,
            obj.clone(),
            DEFAULT_LINE_FILE.clone(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_param_binding_set_on_obj(
        &mut self,
        subject: Obj,
        _set: &Set,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
            subject,
            DEFAULT_LINE_FILE.clone(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_param_binding_nonempty_set_on_obj(
        &mut self,
        subject: Obj,
        _nonempty_set: &NonemptySet,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
            subject,
            DEFAULT_LINE_FILE.clone(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_param_binding_finite_set_on_obj(
        &mut self,
        subject: Obj,
        _finite_set: &FiniteSet,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
            subject,
            DEFAULT_LINE_FILE.clone(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }
}

/// 将 [`FieldAccess`] 转为出现在事实左端的 [`Obj::FieldAccess`]。
#[inline]
fn obj_from_field_access(field_access: &FieldAccess) -> Obj {
    Obj::FieldAccess(field_access.clone())
}

/// 在已有路径上追加一段字段名，得到 `g` + `a.b` → `g.a.b` 形式的 [`FieldAccess`]。
fn append_field_to_field_access(base: &FieldAccess, field_name: &str) -> FieldAccess {
    let mut fields = base.fields.clone();
    fields.push(field_name.to_string());
    FieldAccess::new(base.name.clone(), fields)
}
