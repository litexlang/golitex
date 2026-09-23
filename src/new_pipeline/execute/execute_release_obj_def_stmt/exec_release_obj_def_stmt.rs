//! `release obj def I` — look up StoredIdentifierDefinition and store its facts.
//!
//! Example:
//!   have a R = 2
//!   release obj def a
//!   # stores again (idempotent): a $in R, a = 2

use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::obj::IdentifierObj;
use crate::new_pipeline::ast::stmt::ReleaseObjDefStmt;
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

use super::build_release_facts::BuildReleaseFactsFailed;

pub enum ExecReleaseObjDefStmtFailed {
    DefinitionNotFound { name: IdentifierObj },
    ParamTypeNotReleasable { name: IdentifierObj },
    NameNotInDefinition { name: IdentifierObj },
    FlattenInduc { name: IdentifierObj, reason: String },
    Instantiate { name: IdentifierObj, reason: String },
}

// Mirrored from StoredIdentifierDefinition (minus ParamType).
pub enum ReleaseObjDefByKind {
    LetObj { equal: Fact },
    HaveObjInNonemptySetOrParamType { type_fact: Fact },
    HaveObjEqual { type_fact: Fact, equal: Fact },
    HaveObjByExistFacts {
        type_fact: Fact,
        body_facts: Vec<Fact>,
    },
    TrustHave {
        type_fact: Fact,
        body_facts: Vec<Fact>,
    },
    HaveByReplacementAxiom {
        type_fact: Fact,
        intro: Fact,
        elim: Fact,
    },
    HaveFnEqual {
        membership: Fact,
        equal_to_anon: Fact,
    },
    HaveFnEqualCaseByCase {
        membership: Fact,
        case_foralls: Vec<Fact>,
    },
    HaveFnByForallExistUnique {
        membership: Fact,
        property_forall: Fact,
        uniqueness_forall: Fact,
    },
    HaveFnByInduc {
        membership: Fact,
        case_foralls: Vec<Fact>,
    },
}

// Pipeline: lookup → build facts by kind → store.
pub struct ExecReleaseObjDefStmtSuccess {
    pub statement: ReleaseObjDefStmt,
    pub looked_up: StoredIdentifierDefinition,
    pub released: ReleaseObjDefByKind,
    pub store_and_infer: Vec<StoreFactAndInferResult>,
}

pub enum ExecReleaseObjDefStmtResult {
    Success(ExecReleaseObjDefStmtSuccess),
    Failed(ExecReleaseObjDefStmtFailed),
}

impl ExecReleaseObjDefStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Soft miss: Ok(Failed); operational bug: Err(...).
    pub(in crate::new_pipeline::execute) fn exec_release_obj_def_stmt(
        &mut self,
        stmt: &ReleaseObjDefStmt,
    ) -> RuntimeResult<ExecReleaseObjDefStmtResult> {
        let Some(looked_up) = self.lookup_stored_identifier_definition_for_release(&stmt.name)
        else {
            return Ok(ExecReleaseObjDefStmtResult::Failed(
                ExecReleaseObjDefStmtFailed::DefinitionNotFound {
                    name: stmt.name.clone(),
                },
            ));
        };

        let is_induc = matches!(&looked_up, StoredIdentifierDefinition::HaveFnByInduc(_));
        let built = match self.build_release_obj_def_facts(&stmt.name, &looked_up)? {
            Ok(built) => built,
            Err(failed) => {
                return Ok(ExecReleaseObjDefStmtResult::Failed(map_build_fail(
                    &stmt.name,
                    failed,
                )));
            }
        };

        let store_and_infer = self.store_built_release_facts(&built)?;
        let released = finalize_kind(is_induc, built.kind);

        Ok(ExecReleaseObjDefStmtResult::Success(
            ExecReleaseObjDefStmtSuccess {
                statement: stmt.clone(),
                looked_up,
                released,
                store_and_infer,
            },
        ))
    }
}

fn map_build_fail(
    name: &IdentifierObj,
    failed: BuildReleaseFactsFailed,
) -> ExecReleaseObjDefStmtFailed {
    match failed {
        BuildReleaseFactsFailed::ParamTypeNotReleasable => {
            ExecReleaseObjDefStmtFailed::ParamTypeNotReleasable {
                name: name.clone(),
            }
        }
        BuildReleaseFactsFailed::NameNotInDefinition => {
            ExecReleaseObjDefStmtFailed::NameNotInDefinition {
                name: name.clone(),
            }
        }
        BuildReleaseFactsFailed::FlattenInduc(reason) => ExecReleaseObjDefStmtFailed::FlattenInduc {
            name: name.clone(),
            reason,
        },
        BuildReleaseFactsFailed::Instantiate(reason) => ExecReleaseObjDefStmtFailed::Instantiate {
            name: name.clone(),
            reason,
        },
    }
}

fn finalize_kind(is_induc: bool, kind: ReleaseObjDefByKind) -> ReleaseObjDefByKind {
    if !is_induc {
        return kind;
    }
    match kind {
        ReleaseObjDefByKind::HaveFnEqualCaseByCase {
            membership,
            case_foralls,
        } => ReleaseObjDefByKind::HaveFnByInduc {
            membership,
            case_foralls,
        },
        other => other,
    }
}
