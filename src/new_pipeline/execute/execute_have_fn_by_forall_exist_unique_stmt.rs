//! `have fn name by exist!:` — prove forall+exist!, then store a callable f.
//!
//! Stages: shape → forall WD → FnSet WD → prove forall → store membership +
//! property forall + uniqueness forall.
//!
//! Example:
//! ```text
//! trust forall x A: exist! y B st {$F(x, y)}
//! have fn f by exist!:
//!     ? forall x A:
//!         exist! y B st {$F(x, y)}
//! # stores f $in fn(x A) B and forall x A: $F(x, f(x))
//! ```

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, PlainExistFact,
    QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, FnSet, IdentifierObj, Obj};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::HaveFnByForallExistUniqueStmt;
use crate::new_pipeline::exec_env::{DefinedIdentifierInfo, ExecEnv};
use crate::new_pipeline::execute::execute_by_stmt::{
    proof_verify_state, run_fact_only_proof_steps, verify_goal_fact, ByProofBodyFailed,
    ByProofStepResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecHaveFnByForallExistUniqueStmtFailed {
    Shape(String),
    ForallWellDefined(VerifyFactWellDefinedResult),
    FnSetWellDefined(VerifyObjWellDefinedResult),
    Introduce(String),
    ProofBody(ByProofBodyFailed),
    ForallProof(VerifyFactResult),
    PropertyWellDefined(VerifyFactWellDefinedResult),
}

pub enum HaveFnByExistUniqueProofSuccess {
    ByDirectVerify {
        forall_proof: VerifyFactResult,
    },
    ByProveProcess {
        proof_steps: Vec<ByProofStepResult>,
        conclusion_proofs: Vec<VerifyFactResult>,
        local_env: Box<ExecEnv>,
    },
}

pub struct StoreHaveFnByExistUniqueAndInferResult {
    pub membership_fact_id: FactId,
    pub property_fact_id: FactId,
    pub uniqueness_fact_id: FactId,
    pub stored_fact_ids: Vec<FactId>,
    pub membership_store: StoreFactAndInferResult,
    pub property_store: StoreFactAndInferResult,
    pub uniqueness_store: StoreFactAndInferResult,
}

pub struct ExecHaveFnByForallExistUniqueStmtSuccessResult {
    pub statement: HaveFnByForallExistUniqueStmt,
    pub forall_well_defined: VerifyFactWellDefinedResult,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub proof: HaveFnByExistUniqueProofSuccess,
    pub property_well_defined: VerifyFactWellDefinedResult,
    pub store_and_infer_result: StoreHaveFnByExistUniqueAndInferResult,
}

pub enum ExecHaveFnByForallExistUniqueStmtResult {
    Success(ExecHaveFnByForallExistUniqueStmtSuccessResult),
    Failed(ExecHaveFnByForallExistUniqueStmtFailed),
}

impl ExecHaveFnByForallExistUniqueStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

struct HaveFnByExistUniqueShape {
    fn_set: FnSet,
    witness: BoundName,
    witness_param_type: ParamType,
    body_facts: Vec<QuantifierFreeFact>,
}

impl Runtime {
    pub(super) fn exec_have_fn_by_forall_exist_unique_stmt(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> RuntimeResult<ExecHaveFnByForallExistUniqueStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let shape = match self.have_fn_by_exist_unique_shape(stmt) {
            Ok(s) => s,
            Err(msg) => {
                return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                    ExecHaveFnByForallExistUniqueStmtFailed::Shape(msg),
                ));
            }
        };

        let forall_as_fact = Fact::ForallFact(stmt.forall.clone());
        let forall_well_defined =
            self.verify_fact_well_definedness(&forall_as_fact, verify_state.clone())?;
        if forall_well_defined.is_failed() {
            return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::ForallWellDefined(forall_well_defined),
            ));
        }

        let fn_set_well_defined = self
            .verify_obj_well_definedness(&Obj::FnSet(shape.fn_set.clone()), verify_state.clone())?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let proof = match self.prove_have_fn_by_exist_unique_forall(stmt, &forall_as_fact)? {
            Ok(p) => p,
            Err(failed) => {
                return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(failed));
            }
        };

        // Define f and store membership first so `f(x)` is WD when checking the property.
        let (membership_fact_id, membership_store) =
            self.store_have_fn_by_exist_unique_membership(stmt, &shape.fn_set)?;

        let (property_fact, uniqueness_fact) =
            match self.build_have_fn_by_exist_unique_published_facts(stmt, &shape) {
                Ok(pair) => pair,
                Err(msg) => {
                    return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                        ExecHaveFnByForallExistUniqueStmtFailed::Shape(msg),
                    ));
                }
            };

        let property_well_defined =
            self.verify_fact_well_definedness(&property_fact, verify_state)?;
        if property_well_defined.is_failed() {
            return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::PropertyWellDefined(
                    property_well_defined,
                ),
            ));
        }

        let property_fact_id = property_fact.fact_id();
        let property_store = self.store_fact_and_infer(&property_fact)?;
        let uniqueness_fact_id = uniqueness_fact.fact_id();
        let uniqueness_store = self.store_fact_and_infer(&uniqueness_fact)?;

        let mut stored_fact_ids = membership_store.stored_fact_ids();
        stored_fact_ids.extend(property_store.stored_fact_ids());
        stored_fact_ids.extend(uniqueness_store.stored_fact_ids());

        Ok(ExecHaveFnByForallExistUniqueStmtResult::Success(
            ExecHaveFnByForallExistUniqueStmtSuccessResult {
                statement: stmt.clone(),
                forall_well_defined,
                fn_set_well_defined,
                proof,
                property_well_defined,
                store_and_infer_result: StoreHaveFnByExistUniqueAndInferResult {
                    membership_fact_id,
                    property_fact_id,
                    uniqueness_fact_id,
                    stored_fact_ids,
                    membership_store,
                    property_store,
                    uniqueness_store,
                },
            },
        ))
    }

    fn have_fn_by_exist_unique_shape(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<HaveFnByExistUniqueShape, String> {
        if stmt.forall.then_facts.len() != 1 {
            return Err("forall must have exactly one then fact".to_string());
        }
        let ExistOrAndChainAtomicFact::ExistUniqueFact(plain) = &stmt.forall.then_facts[0] else {
            return Err("forall then must be `exist!`".to_string());
        };
        let (witness, witness_param_type, ret_set) = single_obj_witness(plain)?;
        let set_bound = typed_obj_params_to_set_bound(&stmt.forall.typed_parameters)?;
        Ok(HaveFnByExistUniqueShape {
            fn_set: FnSet {
                set_bound_parameters: set_bound,
                dom_facts: Vec::new(),
                ret_set: Box::new(ret_set),
            },
            witness,
            witness_param_type,
            body_facts: plain.facts.clone(),
        })
    }

    fn prove_have_fn_by_exist_unique_forall(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        forall_as_fact: &Fact,
    ) -> RuntimeResult<
        Result<HaveFnByExistUniqueProofSuccess, ExecHaveFnByForallExistUniqueStmtFailed>,
    > {
        if stmt.prove_process.is_empty() {
            let forall_proof = self.verify_fact(forall_as_fact, proof_verify_state())?;
            if forall_proof.is_failed() {
                return Ok(Err(ExecHaveFnByForallExistUniqueStmtFailed::ForallProof(
                    forall_proof,
                )));
            }
            return Ok(Ok(HaveFnByExistUniqueProofSuccess::ByDirectVerify {
                forall_proof,
            }));
        }

        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            if rt
                .introduce_typed_parameters(&stmt.forall.typed_parameters, proof_verify_state())?
                .is_err()
            {
                return Ok(Err(ExecHaveFnByForallExistUniqueStmtFailed::Introduce(
                    "have fn by exist!: failed to introduce forall parameters".to_string(),
                )));
            }
            for dom in &stmt.forall.dom_facts {
                let wd = rt.verify_fact_well_definedness(dom, proof_verify_state())?;
                if wd.is_failed() {
                    return Ok(Err(ExecHaveFnByForallExistUniqueStmtFailed::Introduce(
                        "have fn by exist!: forall domain fact is not well-defined".to_string(),
                    )));
                }
                let _ = rt.store_fact_and_infer(dom)?;
            }
            let proof_steps = match run_fact_only_proof_steps(rt, &stmt.prove_process)? {
                Ok(steps) => steps,
                Err(body_failed) => {
                    return Ok(Err(ExecHaveFnByForallExistUniqueStmtFailed::ProofBody(
                        body_failed,
                    )));
                }
            };
            let mut conclusion_proofs = Vec::with_capacity(stmt.forall.then_facts.len());
            for then in &stmt.forall.then_facts {
                let then_fact: Fact = then.clone().into();
                let closing = verify_goal_fact(rt, &then_fact)?;
                if closing.is_failed() {
                    return Ok(Err(ExecHaveFnByForallExistUniqueStmtFailed::ForallProof(
                        closing,
                    )));
                }
                conclusion_proofs.push(closing);
            }
            Ok(Ok((proof_steps, conclusion_proofs)))
        })?;

        match inner {
            Ok((proof_steps, conclusion_proofs)) => {
                Ok(Ok(HaveFnByExistUniqueProofSuccess::ByProveProcess {
                    proof_steps,
                    conclusion_proofs,
                    local_env,
                }))
            }
            Err(failed) => Ok(Err(failed)),
        }
    }

    fn build_have_fn_by_exist_unique_published_facts(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByExistUniqueShape,
    ) -> Result<(Fact, Fact), String> {
        let function_ident = self.identifier_obj_for_file_root_symbol(stmt.name.clone());
        let applied = applied_fn_obj(&function_ident, &stmt.forall.typed_parameters);

        let mut witness_to_applied = HashMap::new();
        witness_to_applied.insert(shape.witness.id, applied.clone());

        let mut property_thens = Vec::with_capacity(shape.body_facts.len());
        for body in &shape.body_facts {
            let inst = self
                .inst_quantifier_free_fact(body, &witness_to_applied)
                .map_err(|e| format!("property instantiate: {e}"))?;
            property_thens.push(qf_to_exist_or_and(inst));
        }
        let property = Fact::ForallFact(ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: stmt.forall.typed_parameters.clone(),
            dom_facts: stmt.forall.dom_facts.clone(),
            then_facts: property_thens,
            line_file: Some(stmt.line_file.clone()),
        });

        let mut uniqueness_params = stmt.forall.typed_parameters.clone();
        uniqueness_params.groups.push(TypedParameterGroup {
            params: vec![shape.witness.clone()],
            param_type: shape.witness_param_type.clone(),
        });
        let empty: HashMap<IdentifierId, Obj> = HashMap::new();
        let mut uniqueness_dom = stmt.forall.dom_facts.clone();
        for body in &shape.body_facts {
            let inst = self
                .inst_quantifier_free_fact(body, &empty)
                .map_err(|e| format!("uniqueness instantiate: {e}"))?;
            uniqueness_dom.push(quantifier_free_fact_to_fact(inst));
        }
        let equal_atomic = AtomicFact::EqualFact(EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: Obj::Identifier(IdentifierObj::from_bound_name(&shape.witness)),
            right: applied,
            line_file: Some(stmt.line_file.clone()),
        });
        let uniqueness = Fact::ForallFact(ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: uniqueness_params,
            dom_facts: uniqueness_dom,
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(equal_atomic)],
            line_file: Some(stmt.line_file.clone()),
        });

        Ok((property, uniqueness))
    }

    fn store_have_fn_by_exist_unique_membership(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        fn_set: &FnSet,
    ) -> RuntimeResult<(FactId, StoreFactAndInferResult)> {
        if self.identifier_defined_in_stack(&stmt.name) {
            return Err(RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            stmt.name.clone(),
            DefinedIdentifierInfo {
                identifier: stmt.name.clone(),
            },
        );

        let function_obj =
            Obj::Identifier(self.identifier_obj_for_file_root_symbol(stmt.name.clone()));
        let membership_fact_id = self.ids.allocate_fact_id();
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: membership_fact_id,
            element: function_obj,
            set: Obj::FnSet(fn_set.clone()),
            line_file: Some(stmt.line_file.clone()),
        }));
        let store = self.store_fact_and_infer(&membership)?;
        Ok((membership_fact_id, store))
    }
}

fn single_obj_witness(plain: &PlainExistFact) -> Result<(BoundName, ParamType, Obj), String> {
    let mut found: Option<(BoundName, ParamType, Obj)> = None;
    for group in &plain.typed_parameters.groups {
        for param in &group.params {
            let ParamType::Obj(obj) = &group.param_type else {
                return Err("exist! witness must have an Obj param type".to_string());
            };
            if found.is_some() {
                return Err("exist! must bind exactly one witness".to_string());
            }
            found = Some((
                param.clone(),
                group.param_type.clone(),
                obj.clone(),
            ));
        }
    }
    found.ok_or_else(|| "exist! must bind exactly one witness".to_string())
}

fn typed_obj_params_to_set_bound(
    params: &TypedParameterList,
) -> Result<SetBoundParameterList, String> {
    let mut groups = Vec::new();
    for group in &params.groups {
        let ParamType::Obj(obj) = &group.param_type else {
            return Err("forall parameters must be Obj-typed".to_string());
        };
        groups.push(SetBoundParameterGroup {
            params: group.params.clone(),
            param_type: Box::new(obj.clone()),
        });
    }
    if groups.is_empty() {
        return Err("forall must have at least one parameter".to_string());
    }
    Ok(SetBoundParameterList { groups })
}

fn applied_fn_obj(function_ident: &IdentifierObj, params: &TypedParameterList) -> Obj {
    let mut args = Vec::new();
    for group in &params.groups {
        for param in &group.params {
            args.push(Box::new(Obj::Identifier(IdentifierObj::from_bound_name(
                param,
            ))));
        }
    }
    Obj::FnObj(FnObj {
        head: Box::new(FnObjHead::Identifier(function_ident.clone())),
        body: vec![args],
    })
}

fn qf_to_exist_or_and(qf: QuantifierFreeFact) -> ExistOrAndChainAtomicFact {
    match qf {
        QuantifierFreeFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
        QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
        QuantifierFreeFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
        QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
    }
}
