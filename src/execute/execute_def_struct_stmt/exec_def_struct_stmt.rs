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
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactResult;

pub enum ExecDefStructStmtFailed {
    Local(Box<ExecDefStructLocalFailure>),
    NameClash(String),
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    StructureDomain(FailToVerifyFactWellDefinedResult),
    FieldType(VerifyObjWellDefinedResult),
    EquivalentFact(FailToVerifyFactWellDefinedResult),
}

pub struct ExecDefStructLocalFailure {
    pub statement: DefStructStmt,
    pub failure: DefStructLocalFailed,
    pub local_env: Box<ExecEnv>,
}

pub enum DefStructLocalFailed {
    Parameters(IntroduceTypedParametersFailed),
    Domain {
        introduced_params: Option<IntroduceTypedParametersResult>,
        structure_domains: Vec<FactWellDefinedProof>,
        failed: FailToVerifyFactWellDefinedResult,
    },
    Fields {
        introduced_params: Option<IntroduceTypedParametersResult>,
        structure_domains: Vec<FactWellDefinedProof>,
        field_failure: ExecDefStructFieldLocalFailure,
    },
}

pub struct ExecDefStructFieldLocalFailure {
    pub failure: DefStructFieldLocalFailed,
    pub field_local_env: Box<ExecEnv>,
}

pub enum DefStructFieldLocalFailed {
    Field {
        fields: Vec<StructFieldWellDefinedAndIntroduced>,
        failed: VerifyObjWellDefinedResult,
    },
    Condition {
        fields: Vec<StructFieldWellDefinedAndIntroduced>,
        equivalent_facts: Vec<StructEquivalentFactWellDefinedProof>,
        failed: FailToVerifyFactWellDefinedResult,
    },
}

impl ExecDefStructLocalFailure {
    pub fn new(
        statement: DefStructStmt,
        failure: DefStructLocalFailed,
        local_env: Box<ExecEnv>,
    ) -> Self {
        Self {
            statement,
            failure,
            local_env,
        }
    }
}

impl ExecDefStructFieldLocalFailure {
    pub fn new(failure: DefStructFieldLocalFailed, field_local_env: Box<ExecEnv>) -> Self {
        Self {
            failure,
            field_local_env,
        }
    }
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
    pub auto_opened_struct_layers: Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
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
        if let Some(msg) = self.def_struct_name_clash(&def_struct.name) {
            return Ok(ExecDefStructStmtResult::Failed(
                ExecDefStructStmtFailed::NameClash(msg),
            ));
        }

        let (local_outcome, local_env) =
            self.run_in_local_env_and_take_env(|rt| rt.exec_def_struct_stmt_in_local(def_struct))?;

        let parts = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => {
                return Ok(ExecDefStructStmtResult::Failed(
                    ExecDefStructStmtFailed::Local(Box::new(ExecDefStructLocalFailure::new(
                        def_struct.clone(),
                        failed,
                        local_env,
                    ))),
                ))
            }
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
    fn def_struct_name_clash(&self, name: &str) -> Option<String> {
        if self.def_struct_visible_in_stack(name).is_some() {
            return Some(format!(
                "name `{name}` is already used in this scope as {STRUCT}"
            ));
        }
        None
    }

    fn exec_def_struct_stmt_in_local(
        &mut self,
        def_struct: &DefStructStmt,
    ) -> RuntimeResult<Result<OuterLocalParts, DefStructLocalFailed>> {
        let verify_state = VerifyState::top_level();

        let introduced_params = if let Some((params, _)) = &def_struct.param_def_with_dom {
            match self.introduce_typed_parameters(params, verify_state.clone())? {
                Ok(result) => Some(result),
                Err(failed) => return Ok(Err(DefStructLocalFailed::Parameters(failed))),
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
                        return Ok(Err(DefStructLocalFailed::Domain {
                            introduced_params,
                            structure_domains,
                            failed: reason,
                        }));
                    }
                }
            }
        }

        let (field_outcome, field_local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.exec_def_struct_field_scope(&def_struct.fields, &def_struct.equivalent_facts)
        })?;

        let (fields, equivalent_facts) = match field_outcome {
            Ok(parts) => parts,
            Err(failed) => {
                return Ok(Err(DefStructLocalFailed::Fields {
                    introduced_params,
                    structure_domains,
                    field_failure: ExecDefStructFieldLocalFailure::new(failed, field_local_env),
                }))
            }
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
            DefStructFieldLocalFailed,
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
                        return Ok(Err(DefStructFieldLocalFailed::Field {
                            fields: introduced_fields,
                            failed,
                        }));
                    }
                };
            let field_params = field_typed_parameters(std::slice::from_ref(field));
            let defined =
                self.define_typed_parameters_in_current_env(&field_params, None, verify_state)?;
            let auto_opened_struct_layers = self
                .auto_open_struct_layers_for_typed_parameters(&field_params, verify_state)?
                .map_err(|(_, failed)| {
                    crate::runtime::RuntimeError::Unsupported(format!(
                        "cannot open nested struct field: {}",
                        failed.reason
                    ))
                })?;
            introduced_fields.push(StructFieldWellDefinedAndIntroduced {
                well_defined,
                defined,
                auto_opened_struct_layers,
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
                    return Ok(Err(DefStructFieldLocalFailed::Condition {
                        fields: introduced_fields,
                        equivalent_facts: checked,
                        failed: reason,
                    }));
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
