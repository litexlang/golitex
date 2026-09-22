//! `obtain x, y from thm name(args)` — eliminate a theorem's sole exist conclusion.
//!
//! Mathematical contract:
//! - Prepare the call like `release thm` (`prepare_release_conclusions`).
//! - Verify every domain fact in a **local** environment (do not merge).
//! - The prepared conclusions must be exactly one positive `exist` / `exist!`
//!   (reject zero / multiple / non-exist / `not exist`).
//! - Apply ordinary existential elimination in the **parent** environment.
//! - Do **not** store the release conclusions into the parent.
//!
//! Example:
//!   thm self_exists:
//!       ? forall a R:
//!           exist x R st {x = a}
//!       witness exist x R st {x = a} from a
//!   obtain theorem_copy from thm self_exists(3)
//!   // stores `theorem_copy $in R` and `theorem_copy = 3`

use crate::new_pipeline::ast::fact::{exist_fact_family_from_fact, ExistFactFamily};
use crate::new_pipeline::ast::stmt::ObtainObjFromThm;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_by_stmt::{
    prepare_release_conclusions, verify_goal_fact, ExecReleaseThmStmtFailed, PreparedRelease,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactResult;
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::execute::execute_obtain_obj_from_exist_fact_stmt::ExecObtainObjFromExistFactStmtFailed;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum ExecObtainObjFromThmStmtFailed {
    Release(ExecReleaseThmStmtFailed),
    Dom {
        index: usize,
        result: VerifyFactResult,
    },
    BadConclusions(String),
    Apply(ExecObtainObjFromExistFactStmtFailed),
}

pub struct ExecObtainObjFromThmStmtSuccessResult {
    pub statement: ObtainObjFromThm,
    pub thm_name: String,
    pub dom_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub projected_exist: ExistFactFamily,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecObtainObjFromThmStmtResult {
    Success(ExecObtainObjFromThmStmtSuccessResult),
    Failed(ExecObtainObjFromThmStmtFailed),
}

impl ExecObtainObjFromThmStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Pipeline: prepare_release_conclusions → verify doms in local env
    // → take local_env → sole Exist/ExistUnique → apply in parent.
    pub(super) fn exec_obtain_obj_from_thm_stmt(
        &mut self,
        stmt: &ObtainObjFromThm,
    ) -> RuntimeResult<ExecObtainObjFromThmStmtResult> {
        let thm_name = stmt.call.name.local_name().to_string();
        let prepared = match prepare_release_conclusions(self, &stmt.call)? {
            Ok(p) => p,
            Err(failed) => {
                return Ok(ExecObtainObjFromThmStmtResult::Failed(
                    ExecObtainObjFromThmStmtFailed::Release(failed),
                ));
            }
        };

        let (dom_outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
            verify_release_doms(rt, &prepared)
        })?;

        let dom_proofs = match dom_outcome {
            Ok(p) => p,
            Err(failed) => return Ok(ExecObtainObjFromThmStmtResult::Failed(failed)),
        };

        let projected_exist = match extract_sole_positive_exist_conclusion(&prepared) {
            Ok(family) => family,
            Err(msg) => {
                return Ok(ExecObtainObjFromThmStmtResult::Failed(
                    ExecObtainObjFromThmStmtFailed::BadConclusions(msg),
                ));
            }
        };

        match self.apply_obtain_from_known_exist_family(&projected_exist, &stmt.equal_tos)? {
            Ok(store_and_infer_result) => Ok(ExecObtainObjFromThmStmtResult::Success(
                ExecObtainObjFromThmStmtSuccessResult {
                    statement: stmt.clone(),
                    thm_name,
                    dom_proofs,
                    local_env,
                    projected_exist,
                    store_and_infer_result,
                },
            )),
            Err(failed) => Ok(ExecObtainObjFromThmStmtResult::Failed(
                ExecObtainObjFromThmStmtFailed::Apply(failed),
            )),
        }
    }
}

fn verify_release_doms(
    runtime: &mut Runtime,
    prepared: &PreparedRelease,
) -> RuntimeResult<Result<Vec<VerifyFactResult>, ExecObtainObjFromThmStmtFailed>> {
    let mut dom_proofs = Vec::with_capacity(prepared.dom_facts.len());
    for (index, dom) in prepared.dom_facts.iter().enumerate() {
        let proof = verify_goal_fact(runtime, dom)?;
        if proof.is_failed() {
            return Ok(Err(ExecObtainObjFromThmStmtFailed::Dom {
                index,
                result: proof,
            }));
        }
        dom_proofs.push(proof);
    }
    Ok(Ok(dom_proofs))
}

fn extract_sole_positive_exist_conclusion(
    prepared: &PreparedRelease,
) -> Result<ExistFactFamily, String> {
    if prepared.conclusions.len() != 1 {
        return Err(format!(
            "obtain from thm requires exactly one direct conclusion, got {}",
            prepared.conclusions.len()
        ));
    }
    match exist_fact_family_from_fact(&prepared.conclusions[0]) {
        Some(ExistFactFamily::Exist(p)) => Ok(ExistFactFamily::Exist(p)),
        Some(ExistFactFamily::ExistUnique(p)) => Ok(ExistFactFamily::ExistUnique(p)),
        Some(ExistFactFamily::NotExist(_)) => Err(
            "obtain from thm cannot eliminate a `not exist` conclusion".to_string(),
        ),
        None => Err(
            "obtain from thm requires its sole direct conclusion to be `exist` or `exist!`"
                .to_string(),
        ),
    }
}
