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
//!
//! ## `self` 与定义体事实 `facts`
//!
//! `struct` 定义里 `<=>:` 之后的事实中，用标识符 [`SELF`]（`"self"`）表示「当前实例」。
//! 在把参数绑定到某次 `struct T(...)` 时，要把 `self` **额外**映射到具体对象再 `instantiate`：
//! - 根参数 `g`：`self ↦ Identifier(g)`；
//! - 嵌套在 field 上（如 `g.h` 又是某个 struct）：`self ↦ FieldAccess(g.h)`。
//!
//! 该映射与形参代入 `param_to_arg_map` **合并**后，对 [`DefParamTypeStructStmt::facts`] 中每条
//! [`OrAndChainAtomicFact`] 调用 [`OrAndChainAtomicFact::instantiate`]，再写入环境（见
//! [`Runtime::store_instantiated_struct_def_facts_with_self`]）。
//!
//! ## [`Environment::cache_well_defined_obj`]
//!
//! - 字段类型事实（[`define_param_binding_for_param_type_on_field_access`] 成功）：缓存 `g.add` 等路径。
//! - struct 实例登记（[`register_param_as_struct_instance`]，键为根名 `g` 或嵌套路径 `g.h`）：同样写入缓存。
//! [`verify_field_access_well_defined`] 也会显式查缓存，与顶层 [`Runtime::verify_obj_well_defined_and_store_cache`] 一致。

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
    ///
    /// 成功时：将该路径记入 [`Environment::cache_well_defined_obj`]，便于后续 well-defined 快速通过。
    pub(crate) fn define_param_binding_for_param_type_on_field_access(
        &mut self,
        field_access: &FieldAccess,
        param_type: &ParamType,
    ) -> Result<InferResult, RuntimeError> {
        let subject = obj_from_field_access(field_access);
        let result = match param_type {
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
        };
        if result.is_ok() {
            self.cache_well_defined_for_field_access_path(field_access);
        }
        result
    }

    /// 将 `g.add` 这类路径写入 [`Environment::cache_well_defined_obj`]，与 [`Obj::to_string`] 键一致。
    fn cache_well_defined_for_field_access_path(&mut self, field_access: &FieldAccess) {
        self.top_level_env()
            .cache_well_defined_obj
            .insert(field_access.to_string(), ());
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

        let mut infer_result =
            self.bind_struct_fields_for_root_param(&def, &param_to_arg_map, name)?;
        let fact_infer = self.store_instantiated_struct_def_facts_with_self(
            &def,
            &param_to_arg_map,
            Obj::Identifier(Identifier::new(name.to_string())),
        )?;
        infer_result.new_infer_result_inside(fact_infer);
        Ok(infer_result)
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
    ///
    /// 口语上可称为「在 field access 上绑定 struct」；与根参数分支一样，在字段绑定之后会 **`self` → 本路径**
    /// 并落库 [`DefParamTypeStructStmt::facts`]（见 [`Runtime::store_instantiated_struct_def_facts_with_self`]）。
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
        let fact_infer = self.store_instantiated_struct_def_facts_with_self(
            &def,
            &param_to_arg_map,
            obj_from_field_access(field_access),
        )?;
        infer_result.new_infer_result_inside(fact_infer);
        Ok(infer_result)
    }

    /// 将 `struct` 定义中 `<=>:` 下的 [`DefParamTypeStructStmt::facts`] 做形参代入，并把 `self` 换成当前实例后存库。
    ///
    /// `param_to_arg_map` 来自 [`ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map`]（与字段类型
    /// `instantiate` 使用同一张表）。在此之上插入 `SELF` → `self_replacement`：
    /// - 根绑定：`Obj::Identifier(g)`；
    /// - [`define_param_binding_struct_at_field_access`]（即「在某一 field access 上绑定嵌套 struct」，与
    ///   [`define_param_binding_for_param_type_on_field_access`] 的 `Struct` 分支同源）：`self_replacement`
    ///   为该路径的 [`Obj::FieldAccess`]。
    ///
    /// 这样定义里写的 `self ∈ ...`、`P(self, ...)` 等会在实例化后变成关于 `g` 或 `g.h` 的事实。
    fn store_instantiated_struct_def_facts_with_self(
        &mut self,
        def: &DefParamTypeStructStmt,
        param_to_arg_map: &HashMap<String, Obj>,
        self_replacement: Obj,
    ) -> Result<InferResult, RuntimeError> {
        let mut extended = param_to_arg_map.clone();
        extended.insert(SELF.to_string(), self_replacement);

        let mut infer_result = InferResult::new();
        for fact in def.facts.iter() {
            let instantiated = fact.instantiate(&extended);
            let fr = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(instantiated)
                .map_err(RuntimeError::from)?;
            infer_result.new_infer_result_inside(fr);
        }
        Ok(infer_result)
    }

    /// 写入 [`Environment::defined_field_access_name`]，并把同一字符串键写入 [`Environment::cache_well_defined_obj`]，
    /// 与「字段上已绑定类型」路径共用一套缓存语义，便于 [`verify_field_access_well_defined`]。
    fn register_param_as_struct_instance(&mut self, env_key: &str, inst: InstStructObj) {
        let key = env_key.to_string();
        self.top_level_env()
            .defined_field_access_name
            .insert(key.clone(), inst);
        self.top_level_env()
            .cache_well_defined_obj
            .insert(key, ());
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

fn obj_from_field_access(field_access: &FieldAccess) -> Obj {
    Obj::FieldAccess(field_access.clone())
}

fn append_field_to_field_access(base: &FieldAccess, field_name: &str) -> FieldAccess {
    let mut fields = base.fields.clone();
    fields.push(field_name.to_string());
    FieldAccess::new(base.name.clone(), fields)
}
