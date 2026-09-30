//! `have fn name by exist!:` — choice from unique existence.
//!
//! Pipeline (confirmed):
//! 1. Prove the source `forall` (outside claim/thm/trust) and WD the derived FnSet
//! 2. Store `f $in FnSet(...)` and register InFunctionSet at the definition exit
//!    (no `f = AnonymousFn` / EqualToFunction)
//! 3. Release property forall (`body[y ↦ f(x)]`) and uniqueness forall
//!    (`forall …, y: body ⇒ y = f(x)`, stored like other foralls)
//! 4. Insert `StoredIdentifierDefinition::HaveFnByForallExistUnique` for
//!    `release obj def` (rebuilds the same three facts on the written surface)
//!
//! Template: a `template` **definition** may call this exec as its body check.
//! Instantiating `\Name<args>` installs FnSet membership + property + uniqueness
//! on the instance (same three facts as a plain `have fn by exist!`).
//!
//! ```text
//! trust:
//!     forall x A:
//!         exist! y B st {$F(x, y)}
//! have fn f by exist!:
//!     ? forall x A:
//!         exist! y B st {$F(x, y)}
//! ```

use std::collections::HashMap;

use crate::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, PlainExistFact,
    QuantifierFreeFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{FnObj, FnObjHead, FnSet, IdentifierObj, Obj, FunctionSpace, StructAndFieldAccessObj};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::ast::stmt::{FnSetClause, HaveFnByForallExistUniqueStmt};
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::{
    FailToVerifyFactWellDefinedResult, VerifyFactResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult, VerifyState,
};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveFnByForallExistUniqueStmtFailed {
    SourceForall(VerifyFactResult),
    FnSetWellDefined(VerifyObjWellDefinedResult),
    PropertyWellDefined(FailToVerifyFactWellDefinedResult),
}

// Stages: prove source forall → WD FnSet → membership → property → uniqueness.
pub struct ExecHaveFnByForallExistUniqueStmtSuccessResult {
    pub statement: HaveFnByForallExistUniqueStmt,
    pub source_forall: VerifyFactResult,
    pub fn_set_well_defined: VerifyObjWellDefinedResult,
    pub membership_fact_id: FactId,
    pub property_forall_fact_id: FactId,
    pub uniqueness_forall_fact_id: FactId,
    pub stored_fact_ids: Vec<FactId>,
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

struct HaveFnByExistShape {
    fn_set_clause: FnSetClause,
    witness: BoundName,
    witness_param_type: ParamType,
    exist_body_facts: Vec<QuantifierFreeFact>,
}

impl Runtime {
    // Mathematical contract: unique existence of a witness for each input yields
    // a set-theoretic function `f` in the matching FnSet, the property
    // `body[y ↦ f(x)]`, and the uniqueness direction `body ⇒ y = f(x)`.
    pub(super) fn exec_have_fn_by_forall_exist_unique_stmt(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> RuntimeResult<ExecHaveFnByForallExistUniqueStmtResult> {
        let verify_state = VerifyState {
            can_use_builtin_rule_round: VerifyState::TOP_BUILTIN_RULE_ROUND,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
};

        if self.identifier_defined_in_stack(&stmt.name) {
            return Err(RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                stmt.name
            )));
        }

        let shape = match self.have_fn_by_exist_shape(stmt) {
            Ok(shape) => shape,
            Err(message) => {
                return Err(RuntimeError::InternalBug(format!(
                    "have fn by exist!: {message}"
                )));
            }
        };

        let source_forall =
            self.verify_fact(&Fact::ForallFact(stmt.forall.clone()), verify_state.clone())?;
        if source_forall.is_failed() {
            return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::SourceForall(source_forall),
            ));
        }

        let fn_set = fn_set_from_clause(&shape.fn_set_clause);
        let fn_set_well_defined =
            self.verify_obj_well_definedness(&Obj::FunctionSpace(FunctionSpace::FnSet(fn_set.clone())), verify_state.clone())?;
        if fn_set_well_defined.is_failed() {
            return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                ExecHaveFnByForallExistUniqueStmtFailed::FnSetWellDefined(fn_set_well_defined),
            ));
        }

        let function_ident = self.identifier_obj_for_file_root_symbol(stmt.name.clone());
        let function_obj = Obj::Identifier(function_ident.clone());

        let membership_fact_id = self.global_ids.allocate_fact_id();
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: membership_fact_id,
            element: function_obj,
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: Some(stmt.line_file.clone()),
        }));
        let mut stored_fact_ids = self.store_fact_and_infer(&membership)?.stored_fact_ids();
        if let Fact::AtomicFact(AtomicFact::InFact(in_fact)) = &membership {
            self.record_fn_signature_from_definition_membership(in_fact);
        }

        let applied = applied_function_obj(&Obj::Identifier(function_ident.clone()), &stmt.forall.typed_parameters);
        let property_forall =
            self.build_have_fn_by_exist_property_forall(stmt, &shape, applied.clone())?;
        let property_fact = Fact::ForallFact(property_forall);
        match self.verify_fact_well_definedness(&property_fact, verify_state)? {
            VerifyFactWellDefinedResult::Success(_) => {}
            VerifyFactWellDefinedResult::Failed(reason) => {
                return Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
                    ExecHaveFnByForallExistUniqueStmtFailed::PropertyWellDefined(reason),
                ));
            }
        }
        let property_forall_fact_id = property_fact.fact_id();
        stored_fact_ids.extend(self.store_fact_and_infer(&property_fact)?.stored_fact_ids());

        let uniqueness_forall =
            self.build_have_fn_by_exist_uniqueness_forall(stmt, &shape, applied)?;
        let uniqueness_fact = Fact::ForallFact(uniqueness_forall);
        let uniqueness_forall_fact_id = uniqueness_fact.fact_id();
        stored_fact_ids.extend(self.store_fact_and_infer(&uniqueness_fact)?.stored_fact_ids());

        self.top_exec_env_mut().definitions.identifiers.insert(
            stmt.name.clone(),
            StoredIdentifierDefinition::HaveFnByForallExistUnique((
                stmt.name.clone(),
                Rc::new(stmt.clone()),
            )),
        );

        Ok(ExecHaveFnByForallExistUniqueStmtResult::Success(
            ExecHaveFnByForallExistUniqueStmtSuccessResult {
                statement: stmt.clone(),
                source_forall,
                fn_set_well_defined,
                membership_fact_id,
                property_forall_fact_id,
                uniqueness_forall_fact_id,
                stored_fact_ids,
            },
        ))
    }

    // Rebuild membership + property + uniqueness for `release obj def` (subjects = surface).
    // `surface` is the function subject: plain identifier or InstantiatedTemplateObj.
    pub(crate) fn build_have_fn_by_forall_exist_unique_facts_for_surface(
        &mut self,
        surface: &Obj,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> RuntimeResult<Result<(Fact, Fact, Fact), String>> {
        let shape = match self.have_fn_by_exist_shape(stmt) {
            Ok(shape) => shape,
            Err(message) => return Ok(Err(message)),
        };
        let fn_set = fn_set_from_clause(&shape.fn_set_clause);
        let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: surface.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: Some(stmt.line_file.clone()),
        }));
        let applied = applied_function_obj(surface, &stmt.forall.typed_parameters);
        let property = Fact::ForallFact(
            self.build_have_fn_by_exist_property_forall(stmt, &shape, applied.clone())?,
        );
        let uniqueness = Fact::ForallFact(
            self.build_have_fn_by_exist_uniqueness_forall(stmt, &shape, applied)?,
        );
        Ok(Ok((membership, property, uniqueness)))
    }

    fn have_fn_by_exist_shape(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<HaveFnByExistShape, String> {
        let mut set_bound_groups = Vec::new();
        for group in &stmt.forall.typed_parameters.groups {
            let ParamType::Obj(param_set) = &group.param_type else {
                return Err("forall parameters must all be Obj-typed".to_string());
            };
            set_bound_groups.push(SetBoundParameterGroup {
                params: group.params.clone(),
                param_type: Box::new(param_set.clone()),
            });
        }
        if set_bound_groups.is_empty() {
            return Err("forall must bind at least one Obj parameter".to_string());
        }

        let mut dom_facts = Vec::with_capacity(stmt.forall.dom_facts.len());
        for dom in &stmt.forall.dom_facts {
            let Some(qf) = fact_as_quantifier_free(dom) else {
                return Err(
                    "forall domain facts must be quantifier-free (atomic / and / chain / or)"
                        .to_string(),
                );
            };
            dom_facts.push(qf);
        }

        if stmt.forall.then_facts.len() != 1 {
            return Err("forall must have exactly one then fact".to_string());
        }
        let ExistOrAndChainAtomicFact::ExistUniqueFact(exist_body) = &stmt.forall.then_facts[0]
        else {
            return Err("the only forall then fact must be exist!".to_string());
        };

        let (witness, witness_param_type, ret_set) = single_obj_witness(exist_body)?;

        Ok(HaveFnByExistShape {
            fn_set_clause: FnSetClause {
                set_bound_parameters: SetBoundParameterList {
                    groups: set_bound_groups,
                },
                dom_facts,
                ret_set,
            },
            witness,
            witness_param_type,
            exist_body_facts: exist_body.facts.clone(),
        })
    }

    fn build_have_fn_by_exist_property_forall(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByExistShape,
        applied: Obj,
    ) -> RuntimeResult<ForallFact> {
        let mut subst = HashMap::new();
        subst.insert(shape.witness.id, applied);
        let mut then_facts = Vec::with_capacity(shape.exist_body_facts.len());
        for body in &shape.exist_body_facts {
            let inst = self
                .inst_quantifier_free_fact(body, &subst)
                .map_err(|e| RuntimeError::InternalBug(format!("have fn by exist! property: {e}")))?;
            then_facts.push(quantifier_free_to_exist_or_and_chain(inst));
        }
        Ok(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: stmt.forall.typed_parameters.clone(),
            dom_facts: stmt.forall.dom_facts.clone(),
            then_facts,
            line_file: Some(stmt.line_file.clone()),
        })
    }

    fn build_have_fn_by_exist_uniqueness_forall(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByExistShape,
        applied: Obj,
    ) -> RuntimeResult<ForallFact> {
        let fresh_witness = BoundName::new(
            self.global_ids.allocate_identifier_id(),
            shape.witness.name.clone(),
        );
        let fresh_obj = Obj::Identifier(IdentifierObj::from_bound_name(&fresh_witness));
        let mut subst = HashMap::new();
        subst.insert(shape.witness.id, fresh_obj.clone());

        let mut params = stmt.forall.typed_parameters.groups.clone();
        params.push(TypedParameterGroup {
            params: vec![fresh_witness],
            param_type: shape.witness_param_type.clone(),
        });

        let mut dom_facts = stmt.forall.dom_facts.clone();
        for body in &shape.exist_body_facts {
            let inst = self
                .inst_quantifier_free_fact(body, &subst)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!("have fn by exist! uniqueness: {e}"))
                })?;
            dom_facts.push(quantifier_free_fact_to_fact(inst));
        }

        let equal_fact_id = self.global_ids.allocate_fact_id();
        Ok(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList { groups: params },
            dom_facts,
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact {
                    fact_id: equal_fact_id,
                    left: fresh_obj,
                    right: applied,
                    line_file: Some(stmt.line_file.clone()),
                },
            ))],
            line_file: Some(stmt.line_file.clone()),
        })
    }
}

fn fn_set_from_clause(clause: &FnSetClause) -> FnSet {
    FnSet {
        set_bound_parameters: clause.set_bound_parameters.clone(),
        dom_facts: clause.dom_facts.clone(),
        ret_set: Box::new(clause.ret_set.clone()),
    }
}

fn applied_function_obj(surface: &Obj, params: &TypedParameterList) -> Obj {
    let head = match surface {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::InstantiatedTemplateObj(inst) => FnObjHead::InstantiatedTemplateObj(inst.clone()),
        other => panic!("have fn by exist!: applied head must be identifier or template instance, got {other:?}"),
    };
    let mut args = Vec::new();
    for group in &params.groups {
        for param in &group.params {
            args.push(Box::new(Obj::Identifier(IdentifierObj::from_bound_name(
                param,
            ))));
        }
    }
    Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![args],
    })
}

fn single_obj_witness(
    exist_body: &PlainExistFact,
) -> Result<(BoundName, ParamType, Obj), String> {
    let mut witness: Option<(BoundName, ParamType, Obj)> = None;
    let mut count = 0usize;
    for group in &exist_body.typed_parameters.groups {
        count += group.params.len();
        let ParamType::Obj(ret_set) = &group.param_type else {
            return Err("exist! witness type must be Obj".to_string());
        };
        if let Some(param) = group.params.first() {
            witness = Some((
                param.clone(),
                group.param_type.clone(),
                ret_set.clone(),
            ));
        }
    }
    if count != 1 {
        return Err("exist! must bind exactly one Obj-typed witness".to_string());
    }
    witness.ok_or_else(|| "exist! must bind exactly one Obj-typed witness".to_string())
}

fn fact_as_quantifier_free(fact: &Fact) -> Option<QuantifierFreeFact> {
    match fact {
        Fact::AtomicFact(a) => Some(QuantifierFreeFact::AtomicFact(a.clone())),
        Fact::AndFact(a) => Some(QuantifierFreeFact::AndFact(a.clone())),
        Fact::ChainFact(c) => Some(QuantifierFreeFact::ChainFact(c.clone())),
        Fact::OrFact(o) => Some(QuantifierFreeFact::OrFact(o.clone())),
        _ => None,
    }
}

fn quantifier_free_to_exist_or_and_chain(fact: QuantifierFreeFact) -> ExistOrAndChainAtomicFact {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
        QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
        QuantifierFreeFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
        QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
    }
}
