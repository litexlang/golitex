//! `struct` definition: check WD in nested local scopes, then store globally.
//!
//! Pipeline stages (field order matches Success):
//! Outer local_env:
//!   1. optional header params (param-type WD + define)
//!   2. optional structure-domain fact WD
//!   3. each field-type Obj WD
//! Field local_env (nested):
//!   4. define field identifiers with their carriers
//!   5. equivalent-fact (`<=>:`) WD under those fields
//!   6. close field_local_env into the result
//! Then close outer local_env and store the struct definition in the parent.
//!
//! Example:
//!   struct Point:
//!       x R
//!       y R
//!       <=>:
//!           x = x
//!   // R WD; fields bound in field scope; <=>: WD; Point stored globally

use crate::ast::fact::{Fact, QuantifierFreeFact};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::{DefStructStmt, StructFieldDef};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, ObjWellDefinedProof,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::{
    IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};
use crate::parse::keywords::STRUCT;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecDefStructStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    StructureDomain(FailToVerifyFactWellDefinedResult),
    FieldType(VerifyObjWellDefinedResult),
    EquivalentFact(FailToVerifyFactWellDefinedResult),
}

/// Nested field-binder scope evidence (taken, not merged into the outer local env).
pub struct ExecDefStructFieldScopeSuccessResult {
    pub defined_fields: StoreHaveObjAndInferResult,
    pub equivalent_facts_well_defined: Vec<FactWellDefinedProof>,
    pub field_local_env: Box<ExecEnv>,
}

/// `struct name ...:` pipeline success payload.
pub struct ExecDefStructStmtSuccessResult {
    pub statement: DefStructStmt,
    pub introduced_params: Option<IntroduceTypedParametersResult>,
    pub structure_domains: Vec<FactWellDefinedProof>,
    pub field_type_well_defined: Vec<ObjWellDefinedProof>,
    pub field_scope: ExecDefStructFieldScopeSuccessResult,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecDefStructStmtResult {
    Success(ExecDefStructStmtSuccessResult),
    Failed(ExecDefStructStmtFailed),
}

impl ExecDefStructStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: a struct definition is checked under a temporary
    // header-parameter environment and a nested field binder environment; only
    // the struct definition escapes to the parent. Field carriers and `<=>:`
    // laws must be well-defined under those binders; property release
    // (`release struct def`, `$in &Struct`) is deferred.
    pub(in crate::execute) fn exec_def_struct_stmt(
        &mut self,
        def_struct: &DefStructStmt,
    ) -> RuntimeResult<ExecDefStructStmtResult> {
        self.ensure_def_struct_name_free(&def_struct.name)?;

        let (local_outcome, local_env) = self
            .run_in_local_env_and_take_env(|rt| rt.exec_def_struct_stmt_in_local(def_struct))?;

        let parts = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(ExecDefStructStmtResult::Failed(failed)),
        };

        self.top_exec_env_mut()
            .store_def_struct(def_struct.clone());

        Ok(ExecDefStructStmtResult::Success(
            ExecDefStructStmtSuccessResult {
                statement: def_struct.clone(),
                introduced_params: parts.introduced_params,
                structure_domains: parts.structure_domains,
                field_type_well_defined: parts.field_type_well_defined,
                field_scope: parts.field_scope,
                local_env,
            },
        ))
    }
}

struct OuterLocalParts {
    introduced_params: Option<IntroduceTypedParametersResult>,
    structure_domains: Vec<FactWellDefinedProof>,
    field_type_well_defined: Vec<ObjWellDefinedProof>,
    field_scope: ExecDefStructFieldScopeSuccessResult,
}

impl Runtime {
    fn ensure_def_struct_name_free(&self, name: &str) -> RuntimeResult<()> {
        if self.def_struct_visible_in_stack(name).is_some() {
            return Err(RuntimeError::InternalBug(format!(
                "name `{name}` is already used in this scope as {STRUCT}"
            )));
        }
        Ok(())
    }

    fn exec_def_struct_stmt_in_local(
        &mut self,
        def_struct: &DefStructStmt,
    ) -> RuntimeResult<Result<OuterLocalParts, ExecDefStructStmtFailed>> {
        let verify_state = VerifyState {
            can_use_builtin_rule_round: VerifyState::TOP_BUILTIN_RULE_ROUND,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
};

        let introduced_params = if let Some((params, _)) = &def_struct.param_def_with_dom {
            match self.introduce_typed_parameters(params, verify_state.clone())? {
                Ok(result) => Some(result),
                Err(IntroduceTypedParametersFailed::ParamType(failed)) => {
                    return Ok(Err(ExecDefStructStmtFailed::ParamType(failed)));
                }
                Err(IntroduceTypedParametersFailed::AutoOpenStructLayer { failed, .. }) => {
                    return Ok(Err(ExecDefStructStmtFailed::AutoOpenStructLayer(failed)));
                }
            }
        } else {
            None
        };

        let mut structure_domains = Vec::new();
        if let Some((_, dom_facts)) = &def_struct.param_def_with_dom {
            for dom in dom_facts {
                let fact = fact_from_quantifier_free(dom);
                match self.verify_fact_well_definedness(&fact, verify_state.clone())? {
                    VerifyFactWellDefinedResult::Success(proof) => {
                        structure_domains.push(proof);
                    }
                    VerifyFactWellDefinedResult::Failed(reason) => {
                        return Ok(Err(ExecDefStructStmtFailed::StructureDomain(reason)));
                    }
                }
            }
        }

        let mut field_type_well_defined = Vec::with_capacity(def_struct.fields.len());
        for field in &def_struct.fields {
            match self.verify_obj_well_definedness(&field.field_type, verify_state.clone())? {
                VerifyObjWellDefinedResult::Success(proof) => {
                    field_type_well_defined.push(proof);
                }
                failed @ VerifyObjWellDefinedResult::Failed { .. } => {
                    return Ok(Err(ExecDefStructStmtFailed::FieldType(failed)));
                }
            }
        }

        let (field_outcome, field_local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.exec_def_struct_field_scope(&def_struct.fields, &def_struct.equivalent_facts)
        })?;

        let (defined_fields, equivalent_facts_well_defined) = match field_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(Err(failed)),
        };

        Ok(Ok(OuterLocalParts {
            introduced_params,
            structure_domains,
            field_type_well_defined,
            field_scope: ExecDefStructFieldScopeSuccessResult {
                defined_fields,
                equivalent_facts_well_defined,
                field_local_env,
            },
        }))
    }

    fn exec_def_struct_field_scope(
        &mut self,
        fields: &[StructFieldDef],
        equivalent_facts: &[Fact],
    ) -> RuntimeResult<
        Result<(StoreHaveObjAndInferResult, Vec<FactWellDefinedProof>), ExecDefStructStmtFailed>,
    > {
        let verify_state = VerifyState {
            can_use_builtin_rule_round: VerifyState::TOP_BUILTIN_RULE_ROUND,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
};

        let field_params = field_typed_parameters(fields);
        let defined_fields = self.define_typed_parameters_in_current_env(&field_params, None)?;

        let mut equivalent_facts_well_defined = Vec::with_capacity(equivalent_facts.len());
        for fact in equivalent_facts {
            match self.verify_fact_well_definedness(fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    equivalent_facts_well_defined.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(Err(ExecDefStructStmtFailed::EquivalentFact(reason)));
                }
            }
        }

        Ok(Ok((defined_fields, equivalent_facts_well_defined)))
    }
}

// Reuse parse-time BoundName ids so `<=>:` free refs and InFunctionSet keys match.
fn field_typed_parameters(fields: &[StructFieldDef]) -> TypedParameterList {
    let mut groups = Vec::with_capacity(fields.len());
    for field in fields {
        groups.push(TypedParameterGroup {
            params: vec![field.binding.clone()],
            param_type: ParamType::Obj(field.field_type.clone()),
        });
    }
    TypedParameterList { groups }
}

fn fact_from_quantifier_free(fact: &QuantifierFreeFact) -> Fact {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => Fact::AtomicFact(a.clone()),
        QuantifierFreeFact::AndFact(a) => Fact::AndFact(a.clone()),
        QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c.clone()),
        QuantifierFreeFact::OrFact(o) => Fact::OrFact(o.clone()),
    }
}
