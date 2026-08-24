use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_by_struct_def_stmt(
        &mut self,
        stmt: &ByStructDefStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let membership: AtomicFact = InFact::new(
            stmt.obj.clone(),
            stmt.struct_obj.clone().into(),
            stmt.line_file.clone(),
        )
        .into();
        self.verify_atomic_fact_well_defined(&membership, &ProofSearchState::initial())?;
        let membership_check =
            self.verify_atomic_fact(&membership, &ProofSearchState::initial())?;
        if membership_check.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by struct def `{}`: cannot verify declaration-owned membership `{}`",
                    stmt.obj, membership
                ),
                None,
                vec![membership_check],
            ));
        }

        let infer_result = self.run_in_local_env_and_commit(|runtime| {
            runtime.release_one_struct_definition_layer(
                &stmt.obj,
                &stmt.struct_obj,
                stmt.line_file.clone(),
                ByStructDefStmt::store_reason(),
            )
        })?;
        Ok(
            SuccessByStmtResult::ByStructDefStmt(Box::new(SuccessByStructDefStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                membership_check: Some(Box::new(membership_check)),
            }))
            .into(),
        )
    }

    pub fn exec_by_struct_def_stmt_affect_environment_only(
        &mut self,
        stmt: &ByStructDefStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.release_one_struct_definition_layer(
            &stmt.obj,
            &stmt.struct_obj,
            stmt.line_file.clone(),
            ByStructDefStmt::store_reason(),
        )?;
        Ok(
            SuccessByStmtResult::ByStructDefStmt(Box::new(SuccessByStructDefStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                membership_check: None,
            }))
            .into(),
        )
    }

    /// Release the facts belonging to exactly one declaration-owned struct
    /// layer. Callers must establish the corresponding membership first.
    pub fn release_one_struct_definition_layer(
        &mut self,
        obj: &Obj,
        struct_obj: &StructObj,
        line_file: LineFile,
        store_reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let store_reason = store_reason.into();
        let (def, header_map) =
            self.struct_header_param_to_arg_map(struct_obj, &ProofSearchState::initial())?;
        let mut named_field_map = HashMap::new();
        for field in def.fields.iter() {
            let field_value: Obj = ObjAsStructInstanceWithFieldAccess::new(
                struct_obj.clone(),
                obj.clone(),
                field.name().to_string(),
            )
            .into();
            insert_symbol_substitution(&mut named_field_map, &field.binding, field_value);
        }

        let mut field_types = Vec::with_capacity(def.fields.len());
        for field in def.fields.iter() {
            let after_header =
                self.inst_obj(&field.field_type, &header_map, ParamObjType::DefHeader)?;
            field_types.push(self.inst_obj(
                &after_header,
                &named_field_map,
                ParamObjType::DefStructField,
            )?);
        }

        let mut infer_result = SuccessInferResult::new();
        if def.fields.len() > 1 {
            let cart = Cart::new(field_types.clone());
            self.store_tuple_obj_and_cart(
                &obj.to_string(),
                None,
                Some(cart.clone()),
                line_file.clone(),
            );
            let is_tuple: AtomicFact = IsTupleFact::new(obj.clone(), line_file.clone()).into();
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    is_tuple,
                    store_reason.clone(),
                )?,
            );
            let tuple_dim: AtomicFact = EqualFact::new(
                TupleDim::new(obj.clone()).into(),
                Number::new(def.fields.len().to_string()).into(),
                line_file.clone(),
            )
            .into();
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    tuple_dim,
                    store_reason.clone(),
                )?,
            );
            let cart_membership: AtomicFact =
                InFact::new(obj.clone(), cart.into(), line_file.clone()).into();
            infer_result.new_infer_result_inside(
                self.store_derived_atomic_fact_without_infer(
                    cart_membership,
                    store_reason.clone(),
                )?,
            );
        }

        for field in def.fields.iter() {
            let field_value: Obj = ObjAsStructInstanceWithFieldAccess::new(
                struct_obj.clone(),
                obj.clone(),
                field.name().to_string(),
            )
            .into();
            let projection = self.struct_field_access_projection(match &field_value {
                Obj::ObjAsStructInstanceWithFieldAccess(access) => access,
                _ => unreachable!("constructed field access has the field-access shape"),
            })?;
            let bridge: AtomicFact =
                EqualFact::new(field_value, projection, line_file.clone()).into();
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    bridge,
                    store_reason.clone(),
                )?,
            );
        }

        for (field, named_field_type) in def.fields.iter().zip(field_types.iter()) {
            let field_value: Obj = ObjAsStructInstanceWithFieldAccess::new(
                struct_obj.clone(),
                obj.clone(),
                field.name().to_string(),
            )
            .into();
            let field_membership: AtomicFact =
                InFact::new(field_value, named_field_type.clone(), line_file.clone()).into();
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    field_membership,
                    store_reason.clone(),
                )?,
            );
            if def.fields.len() == 1 {
                let carrier_membership: AtomicFact =
                    InFact::new(obj.clone(), named_field_type.clone(), line_file.clone()).into();
                infer_result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                        carrier_membership,
                        store_reason.clone(),
                    )?,
                );
            }
        }

        for fact in def.equivalent_facts.iter() {
            let after_header = self.inst_fact(
                fact,
                &header_map,
                ParamObjType::DefHeader,
                Some(line_file.clone()),
            )?;
            let named_fact = self.inst_fact(
                &after_header,
                &named_field_map,
                ParamObjType::DefStructField,
                Some(line_file.clone()),
            )?;
            infer_result.new_infer_result_inside(
                self.store_fact_without_forall_coverage_check_and_infer_with_reason(
                    named_fact,
                    store_reason.clone(),
                )?,
            );
            if def.fields.len() == 1 {
                // A one-field struct is an identity view of its sole carrier:
                // both `e.only` and `e` denote the value governed by the
                // struct laws.  Store the carrier spelling as part of this
                // explicit release so clients do not depend on arbitrary
                // deep congruence rewriting through every predicate.
                let mut carrier_field_map = HashMap::new();
                insert_symbol_substitution(
                    &mut carrier_field_map,
                    &def.fields[0].binding,
                    obj.clone(),
                );
                let carrier_fact = self.inst_fact(
                    &after_header,
                    &carrier_field_map,
                    ParamObjType::DefStructField,
                    Some(line_file.clone()),
                )?;
                infer_result.new_infer_result_inside(
                    self.store_fact_without_forall_coverage_check_and_infer_with_reason(
                        carrier_fact,
                        store_reason.clone(),
                    )?,
                );
            }
        }

        Ok(infer_result)
    }
}
