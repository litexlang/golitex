//! `struct` definition: check WD in nested local scopes, then store globally.
//!
//! Pipeline stages (field order matches Success):
//! Outer local_env:
//!   1. optional header params (param-type WD + define)
//!   2. optional structure-domain fact WD
//! Field local_env (nested):
//!   3. each field-type Obj WD under the header and earlier fields
//!   4. introduce that field, then continue with the next field
//!   5. equivalent-fact (`<=>:`) WD under those fields
//!   6. close field_local_env into the result
//! Then close outer local_env, store the struct definition and publish quantified laws
//! in the parent statement transaction.
//!
//! Example:
//!   struct Point:
//!       x R
//!       y R
//!       <=>:
//!           x = x
//!   // R WD; fields bound in field scope; <=>: WD; Point stored globally

use super::store_struct_definition_facts::StoreStructDefinitionFactResult;
use crate::ast::fact::{Fact, QuantifierFreeFact};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::{DefStructStmt, StructFieldDef};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, ObjWellDefinedProof,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::{IntroduceTypedParametersFailed, IntroduceTypedParametersResult};
use crate::parse::keywords::STRUCT;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::store_fact_and_infer::StoreFactResult;

pub enum ExecDefStructStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    StructureDomain(FailToVerifyFactWellDefinedResult),
    FieldType(VerifyObjWellDefinedResult),
    EquivalentFact(FailToVerifyFactWellDefinedResult),
}

/// Nested field-binder scope evidence (taken, not merged into the outer local env).
pub struct ExecDefStructFieldScopeSuccessResult {
    pub fields: Vec<StructFieldWellDefinedAndIntroduced>,
    pub equivalent_facts: Vec<StructEquivalentFactWellDefinedProof>,
    pub field_local_env: Box<ExecEnv>,
}

/// One ordered field stage: check its carrier before introducing its binding.
pub struct StructFieldWellDefinedAndIntroduced {
    pub well_defined: ObjWellDefinedProof,
    pub defined: StoreHaveObjAndInferResult,
}

// Each condition is checked before it is assumed for subsequent conditions.
// These stores belong only to the field binder environment.
pub struct StructEquivalentFactWellDefinedProof {
    pub well_defined: FactWellDefinedProof,
    pub store: StoreFactResult,
}

/// `struct name ...:` pipeline success payload.
pub struct ExecDefStructStmtSuccessResult {
    pub statement: DefStructStmt,
    pub introduced_params: Option<IntroduceTypedParametersResult>,
    pub structure_domains: Vec<FactWellDefinedProof>,
    pub field_scope: ExecDefStructFieldScopeSuccessResult,
    pub local_env: Box<ExecEnv>,
    pub definition_facts: Vec<StoreStructDefinitionFactResult>,
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
    // header-parameter environment and a nested field binder environment.
    // Publish the definition and its quantified laws in the statement transaction;
    // local field assumptions never escape as unquantified ambient facts.
    pub(in crate::execute) fn exec_def_struct_stmt(
        &mut self,
        def_struct: &DefStructStmt,
    ) -> RuntimeResult<ExecDefStructStmtResult> {
        self.ensure_def_struct_name_free(&def_struct.name)?;

        let (local_outcome, local_env) =
            self.run_in_local_env_and_take_env(|rt| rt.exec_def_struct_stmt_in_local(def_struct))?;

        let parts = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(ExecDefStructStmtResult::Failed(failed)),
        };

        self.top_exec_env_mut().store_def_struct(def_struct.clone());
        let definition_facts = self.store_struct_definition_facts(
            def_struct,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;

        Ok(ExecDefStructStmtResult::Success(
            ExecDefStructStmtSuccessResult {
                statement: def_struct.clone(),
                introduced_params: parts.introduced_params,
                structure_domains: parts.structure_domains,
                field_scope: parts.field_scope,
                local_env,
                definition_facts,
            },
        ))
    }
}

struct OuterLocalParts {
    introduced_params: Option<IntroduceTypedParametersResult>,
    structure_domains: Vec<FactWellDefinedProof>,
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
        let verify_state = VerifyState::top_level();

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

        let (field_outcome, field_local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.exec_def_struct_field_scope(&def_struct.fields, &def_struct.equivalent_facts)
        })?;

        let (fields, equivalent_facts) = match field_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(Err(failed)),
        };

        Ok(Ok(OuterLocalParts {
            introduced_params,
            structure_domains,
            field_scope: ExecDefStructFieldScopeSuccessResult {
                fields,
                equivalent_facts,
                field_local_env,
            },
        }))
    }

    fn exec_def_struct_field_scope(
        &mut self,
        fields: &[StructFieldDef],
        equivalent_facts: &[Fact],
    ) -> RuntimeResult<
        Result<
            (
                Vec<StructFieldWellDefinedAndIntroduced>,
                Vec<StructEquivalentFactWellDefinedProof>,
            ),
            ExecDefStructStmtFailed,
        >,
    > {
        let verify_state = VerifyState::top_level();

        let mut introduced_fields = Vec::with_capacity(fields.len());
        for field in fields {
            // The current field is not in scope until its type has passed WD.
            // Earlier field assumptions remain confined to this field scope.
            let well_defined =
                match self.verify_obj_well_definedness(&field.field_type, verify_state)? {
                    VerifyObjWellDefinedResult::Success(proof) => proof,
                    failed @ VerifyObjWellDefinedResult::Failed { .. } => {
                        return Ok(Err(ExecDefStructStmtFailed::FieldType(failed)));
                    }
                };
            let field_params = field_typed_parameters(std::slice::from_ref(field));
            let defined =
                self.define_typed_parameters_in_current_env(&field_params, None, verify_state)?;
            introduced_fields.push(StructFieldWellDefinedAndIntroduced {
                well_defined,
                defined,
            });
        }

        let mut checked = Vec::with_capacity(equivalent_facts.len());
        for fact in equivalent_facts {
            match self.verify_fact_well_definedness(fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    let store = self.store_fact(fact)?;
                    checked.push(StructEquivalentFactWellDefinedProof {
                        well_defined: proof,
                        store,
                    });
                }
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(Err(ExecDefStructStmtFailed::EquivalentFact(reason)));
                }
            }
        }

        Ok(Ok((introduced_fields, checked)))
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

#[cfg(test)]
#[path = "../../../tests/unit/execute/struct_ordered_conditions/tests.rs"]
mod ordered_condition_tests;

#[cfg(test)]
#[path = "../../../tests/unit/execute/struct_dependent_fields/tests.rs"]
mod dependent_field_tests;
