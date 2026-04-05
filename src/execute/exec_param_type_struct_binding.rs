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
//! 左端为 `FieldAccess { name: "g", field: "id" }` 对应的 [`Obj::FieldAccess`]。
//!
//! ## `self` 与定义体事实 `facts`
//!
//! `struct` 定义里 `<=>:` 之后的事实中，用标识符 [`SELF`]（`"self"`）表示「当前实例」。
//! 在把参数绑定到某次 `struct T(...)` 时，要把 `self` **额外**映射到具体对象再 `instantiate`：
//! - 根参数 `g`：`self ↦ Identifier(g)`；
//! - 嵌套在 field 上（如 `g.h` 又是某个 struct）：`self ↦ FieldAccess(g.h)`。
//!
//! 该映射与形参代入 `param_to_arg_map` **合并**后，对 [`DefParamTypeStructStmt::facts`] 中每条
//! [`OrAndChainAtomicFact`] 经 [`Runtime::inst_or_and_chain_atomic_fact`] 代入后，再写入环境（见
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
    /// - `field_access`：已解析好的访问路径，如 `g.id` → [`FieldAccess::new`] `("g", "id")`。
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

    pub(crate) fn define_parameter_by_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        self.register_param_as_struct_instance(name, struct_ty.clone());
        Ok(InferResult::new())
    }

    fn define_param_binding_struct_at_field_access(
        &mut self,
        field_access: &FieldAccess,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_definition_of_struct(&struct_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "struct `{}` is not defined (needed for field `{}` of type `struct {}(...)`)",
                        struct_name,
                        field_access,
                        struct_name
                    ),
                    default_line_file(),
                    None,
                    None,
                ).into());
            }
        };

        let expected_count = ParamGroupWithStructFieldType::number_of_params(&def.param_defs);
        if struct_ty.args.len() != expected_count {
            return Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "struct `{}` expects {} type argument(s), got {}",
                        struct_name,
                        expected_count,
                        struct_ty.args.len()
                    ),
                    default_line_file(),
                    None,
                    None,
                )
                .into(),
            );
        }

        let param_to_arg_map =
            ParamGroupWithStructFieldType::param_defs_and_args_to_param_to_arg_map(
                &def.param_defs,
                &struct_ty.args,
            );

        let mut infer_result = InferResult::new();
        for (field_name, field_param_type) in def.fields.iter() {
            let instantiated =
                self.inst_param_type(&field_param_type.to_param_type(), &param_to_arg_map)?;
            let fa = append_field_to_field_access(field_access, field_name);
            let fr =
                self.define_param_binding_for_param_type_on_field_access(&fa, &instantiated)?;
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

    /// 元组实参与 `struct T(...)` 一一对应 [`DefParamTypeStructStmt::fields`]（含头部形参对应的隐式 field），
    /// 各分量再按字段类型做 [`define_param_binding_for_param_type_on_obj`]；`<=>:` 下事实里 `self` 代换为整段 tuple，
    /// 并临时登记 `SELF` → [`InstStructObj`] 以便实例化时 `self.<field>` 能投影到分量。
    fn define_param_binding_struct_from_tuple(
        &mut self,
        tuple: &Tuple,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_definition_of_struct(&struct_name) {
            Some(d) => d,
            None => {
                return Err(
                    RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                        format!("struct `{}` is not defined", struct_name),
                        default_line_file(),
                        None,
                        None,
                    )
                    .into(),
                );
            }
        };
        if def.name != struct_name {
            return Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "struct type name `{}` does not match definition name `{}`",
                        struct_name, def.name
                    ),
                    default_line_file(),
                    None,
                    None,
                )
                .into(),
            );
        }

        let expected_count = ParamGroupWithStructFieldType::number_of_params(&def.param_defs);
        if struct_ty.args.len() != expected_count {
            return Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "struct `{}` expects {} type argument(s), got {}",
                        struct_name,
                        expected_count,
                        struct_ty.args.len()
                    ),
                    default_line_file(),
                    None,
                    None,
                )
                .into(),
            );
        }

        if tuple.args.len() != def.fields.len() + def.number_of_params() {
            return Err(RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                format!(
                    "struct `{}`: tuple has {} component(s), definition has {} field(s) (must match)",
                    struct_name,
                    tuple.args.len(),
                    def.fields.len()
                ),
                default_line_file(),
                None,
                None,
            ).into());
        }

        let param_to_arg_map =
            ParamGroupWithStructFieldType::param_defs_and_args_to_param_to_arg_map(
                &def.param_defs,
                &struct_ty.args,
            );

        let mut infer_result = InferResult::new();
        for (i, (_field_name, field_pt)) in def.fields.iter().enumerate() {
            let instantiated =
                self.inst_param_type(&field_pt.to_param_type(), &param_to_arg_map)?;
            let component = (*tuple.args[i + def.number_of_params()]).clone();
            let ir = self.define_param_binding_for_param_type_on_obj(component, &instantiated)?;
            infer_result.new_infer_result_inside(ir);
        }

        let fact_ir = self.store_instantiated_struct_def_facts_with_self(
            &def,
            &param_to_arg_map,
            Obj::Tuple(tuple.clone()),
        )?;
        infer_result.new_infer_result_inside(fact_ir);
        Ok(infer_result)
    }

    /// 将 `struct` 定义中 `<=>:` 下的 [`DefParamTypeStructStmt::facts`] 做形参代入，并把 `self` 换成当前实例后存库。
    ///
    /// `param_to_arg_map` 来自 [`ParamGroupWithStructFieldType::param_defs_and_args_to_param_to_arg_map`]（与字段类型
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
            let instantiated = self.inst_or_and_chain_atomic_fact(fact, &extended)?;
            let fr = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    instantiated,
                )
                .map_err(RuntimeError::from)?;
            infer_result.new_infer_result_inside(fr);
        }
        Ok(infer_result)
    }

    pub fn register_param_as_struct_instance(&mut self, env_key: &str, inst: StructParamType) {
        let key = env_key.to_string();
        self.top_level_env()
            .known_identifier_satisfy_struct
            .insert(key.clone(), inst);
        self.top_level_env()
            .cache_well_defined_obj
            .insert(key.clone(), ());
        self.top_level_env().defined_identifiers.insert(key, ());
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
                return Err(
                    RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                        format!("family `{}` is not defined", family_name),
                        default_line_file(),
                        None,
                        None,
                    )
                    .into(),
                );
            }
        };
        let expected_count = ParamGroupWithParamType::number_of_params(&def.params_def_with_type);
        if family_ty.params.len() != expected_count {
            return Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "family `{}` expects {} type argument(s), got {}",
                        family_name,
                        expected_count,
                        family_ty.params.len()
                    ),
                    default_line_file(),
                    None,
                    None,
                )
                .into(),
            );
        }
        let param_to_arg_map = ParamGroupWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_ty.params,
        );
        let member_set = self.inst_obj(&def.equal_to, &param_to_arg_map)?;
        let type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            subject,
            member_set,
            default_line_file(),
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
            default_line_file(),
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
            default_line_file(),
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
            default_line_file(),
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
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    /// 与 [`define_param_binding_for_param_type`](crate::execute::exec_def_stmt) 一致，但左端为任意 [`Obj`]
    ///（标识符、field access 或其它表达式）；与 `store_args_satisfy_param_def`（`runtime_store_arg_satisfy_param_def`）共用此路径。
    pub(crate) fn define_param_binding_for_param_type_on_obj(
        &mut self,
        subject: Obj,
        param_type: &ParamType,
    ) -> Result<InferResult, RuntimeError> {
        match &subject {
            Obj::Identifier(id) => self.define_parameter_by_binding_param_type(&id.name, param_type),
            Obj::FieldAccess(fa) => {
                self.define_param_binding_for_param_type_on_field_access(fa, param_type)
            }
            Obj::Tuple(tuple) => {
                if let ParamType::Struct(struct_ty) = param_type {
                    self.define_param_binding_struct_from_tuple(tuple, struct_ty)
                } else {
                    Err(RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                        format!(
                            "tuple as subject is only supported for struct parameter type, got {}",
                            param_type
                        ),
                        default_line_file(),
                        None,
                        None,
                    ).into())
                }
            }
            _ => match param_type {
                ParamType::Struct(_) => Err(RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "struct parameter type requires an identifier, field access, or tuple matching struct fields, got {}",
                        subject
                    ),
                    default_line_file(),
                    None,
                    None,
                ).into()),
                ParamType::Family(family_ty) => {
                    self.define_param_binding_family_on_obj(subject.clone(), family_ty)
                }
                ParamType::Obj(obj) => self.define_param_binding_obj_on_obj(subject.clone(), obj),
                ParamType::Set(set) => self.define_param_binding_set_on_obj(subject.clone(), set),
                ParamType::NonemptySet(nonempty_set) => {
                    self.define_param_binding_nonempty_set_on_obj(subject.clone(), nonempty_set)
                }
                ParamType::FiniteSet(finite_set) => {
                    self.define_param_binding_finite_set_on_obj(subject.clone(), finite_set)
                }
            },
        }
    }
}

fn obj_from_field_access(field_access: &FieldAccess) -> Obj {
    Obj::FieldAccess(field_access.clone())
}

fn append_field_to_field_access(base: &FieldAccess, field_name: &str) -> FieldAccess {
    base.with_appended_field(field_name)
}
