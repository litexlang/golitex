//! `obtain x, y from exist …` / `exist!` — name witnesses from a known existential.
//!
//! Mathematical contract:
//! - The source `exist` / `exist!` fact must already be known.
//! - `equal_tos` length must match the existential binders.
//! - Each obtained name is introduced with the binder's (possibly dependent)
//!   parameter type, and each existential body fact is stored after renaming.
//! - For `exist!`, also store the uniqueness forall over two witness copies
//!   whose premises are the body facts and whose conclusion equates the copies
//!   (tuple equality when there are several binders).
//!
//! Example:
//!   witness exist u R st {u = 0} from 0
//!   obtain w from exist u R st {u = 0}
//!   // stores `w $in R` and `w = 0`

use std::collections::HashMap;

use crate::ast::fact::{
    AndFact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, ExistShapedFact, Fact, ForallFact,
    PlainExistFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, Obj, Tuple, ProductShape};
use crate::ast::param::{TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::ObtainObjFromExistFact;
use crate::execute::execute_fact_stmt::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyExistUniqueFactResult,
    VerifyExistUniqueFactSuccess, VerifyFactResult, VerifyPlainExistFactResult,
    VerifyPlainExistFactSuccess, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{IdentifierId, Runtime, RuntimeError, RuntimeResult};

pub enum ExecObtainObjFromExistFactStmtFailed {
    ArityMismatch { expected: usize, got: usize },
    NotExistSource,
    Exist(VerifyExistShapedFactFailed),
}

pub enum ObtainExistVerifySuccess {
    Exist(VerifyPlainExistFactSuccess),
    ExistUnique(VerifyExistUniqueFactSuccess),
}

// Pipeline: verify known exist → rename binders → define + store body
// → (exist!) store uniqueness forall.
pub struct ExecObtainObjFromExistFactStmtSuccessResult {
    pub statement: ObtainObjFromExistFact,
    pub verify_exist: ObtainExistVerifySuccess,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecObtainObjFromExistFactStmtResult {
    Success(ExecObtainObjFromExistFactStmtSuccessResult),
    Failed(ExecObtainObjFromExistFactStmtFailed),
}

impl ExecObtainObjFromExistFactStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    pub(super) fn exec_obtain_obj_from_exist_fact_stmt(
        &mut self,
        stmt: &ObtainObjFromExistFact,
    ) -> RuntimeResult<ExecObtainObjFromExistFactStmtResult> {
        if matches!(stmt.fact, ExistShapedFact::NotExist(_)) {
            return Ok(ExecObtainObjFromExistFactStmtResult::Failed(
                ExecObtainObjFromExistFactStmtFailed::NotExistSource,
            ));
        }

        let verify_state = VerifyState {
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };
        let verified = self.verify_exist_shaped_fact(&stmt.fact, verify_state)?;
        let verify_exist = match self.unwrap_obtain_exist_verify(verified)? {
            Ok(success) => success,
            Err(failed) => {
                return Ok(ExecObtainObjFromExistFactStmtResult::Failed(
                    ExecObtainObjFromExistFactStmtFailed::Exist(failed),
                ));
            }
        };

        match self.apply_obtain_from_known_exist_family(&stmt.fact, &stmt.equal_tos)? {
            Ok(store_and_infer_result) => Ok(ExecObtainObjFromExistFactStmtResult::Success(
                ExecObtainObjFromExistFactStmtSuccessResult {
                    statement: stmt.clone(),
                    verify_exist,
                    store_and_infer_result,
                },
            )),
            Err(failed) => Ok(ExecObtainObjFromExistFactStmtResult::Failed(failed)),
        }
    }

    // Shared eliminator for a known Exist / ExistUnique family (no verify).
    // Used by obtain-from-exist and obtain-from-$P.
    // For exist!, uniqueness forall is stored into Env via store_and_infer_result
    // (no separate id field — resolve through Env / stored_fact_ids).
    pub(in crate::execute) fn apply_obtain_from_known_exist_family(
        &mut self,
        family: &ExistShapedFact,
        equal_tos: &[String],
    ) -> RuntimeResult<Result<StoreHaveObjAndInferResult, ExecObtainObjFromExistFactStmtFailed>>
    {
        if matches!(family, ExistShapedFact::NotExist(_)) {
            return Ok(Err(ExecObtainObjFromExistFactStmtFailed::NotExistSource));
        }

        let plain = family.plain();
        let expected = plain.typed_parameters.ordered_param_ids().len();
        let got = equal_tos.len();
        if expected != got {
            return Ok(Err(ExecObtainObjFromExistFactStmtFailed::ArityMismatch {
                expected,
                got,
            }));
        }

        let (renamed_params, subst) =
            self.build_obtain_renamed_params_and_subst(plain, equal_tos)?;

        let mut store_and_infer_result =
            self.define_typed_parameters_in_current_env(&renamed_params, None)?;

        for body_fact in &plain.facts {
            let instantiated = self
                .inst_quantifier_free_fact(body_fact, &subst)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!(
                        "obtain: failed to instantiate existential body: {e}"
                    ))
                })?;
            let as_fact = quantifier_free_fact_to_fact(instantiated);
            let stored = self.store_fact_and_infer(&as_fact)?;
            store_and_infer_result
                .stored_fact_ids
                .extend(stored.stored_fact_ids());
        }

        if matches!(family, ExistShapedFact::ExistUnique(_)) {
            let uniqueness = self.build_exist_unique_uniqueness_forall_fact(plain)?;
            let stored = self.store_fact_and_infer(&Fact::ForallFact(uniqueness))?;
            store_and_infer_result
                .stored_fact_ids
                .extend(stored.stored_fact_ids());
        }

        Ok(Ok(store_and_infer_result))
    }

    fn unwrap_obtain_exist_verify(
        &self,
        result: VerifyFactResult,
    ) -> RuntimeResult<Result<ObtainExistVerifySuccess, VerifyExistShapedFactFailed>> {
        match result {
            VerifyFactResult::ExistShapedFact(boxed) => match *boxed {
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(s)) => {
                    Ok(Ok(ObtainExistVerifySuccess::Exist(s)))
                }
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(f)) => {
                    Ok(Err(f))
                }
                VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(s)) => {
                    Ok(Ok(ObtainExistVerifySuccess::ExistUnique(s)))
                }
                VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(f)) => {
                    Ok(Err(f))
                }
                _ => Err(RuntimeError::InternalBug(
                    "obtain: expected exist / exist! verify result, got unexpected exist family branch"
                        .to_string(),
                )),
            },
            _ => Err(RuntimeError::InternalBug(
                "obtain: expected ExistFact verify result".to_string(),
            )),
        }
    }

    fn build_obtain_renamed_params_and_subst(
        &mut self,
        plain: &PlainExistFact,
        equal_tos: &[String],
    ) -> RuntimeResult<(TypedParameterList, HashMap<IdentifierId, Obj>)> {
        let mut subst = HashMap::new();
        let mut groups = Vec::new();
        let mut equal_index = 0usize;

        for group in &plain.typed_parameters.groups {
            let param_type = self
                .inst_param_type(&group.param_type, &subst)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!(
                        "obtain: failed to instantiate parameter type: {e}"
                    ))
                })?;
            let mut params = Vec::new();
            for old in &group.params {
                let name = equal_tos[equal_index].clone();
                equal_index += 1;
                let id = self.resolve_plain_atom(&name)?;
                let bound = BoundName::new(id, name);
                let obj = Obj::Identifier(self.identifier_obj_for_stored_mention(&bound));
                subst.insert(old.id, obj);
                params.push(bound);
            }
            groups.push(TypedParameterGroup { params, param_type });
        }

        Ok((TypedParameterList { groups }, subst))
    }

    // Uniqueness forall for `exist!` (tuple conclusion when several binders).
    // Used by obtain; infer prefers componentwise — see `build_exist_unique_component_uniqueness_forall_fact`.
    pub(crate) fn build_exist_unique_uniqueness_forall_fact(
        &mut self,
        plain: &PlainExistFact,
    ) -> RuntimeResult<ForallFact> {
        self.build_exist_unique_uniqueness_forall_fact_inner(plain, false)
    }

    // Manual / legacy infer: multi-binder uniqueness concludes componentwise equals (and of equals).
    pub(crate) fn build_exist_unique_component_uniqueness_forall_fact(
        &mut self,
        plain: &PlainExistFact,
    ) -> RuntimeResult<ForallFact> {
        self.build_exist_unique_uniqueness_forall_fact_inner(plain, true)
    }

    fn build_exist_unique_uniqueness_forall_fact_inner(
        &mut self,
        plain: &PlainExistFact,
        component_conclusion: bool,
    ) -> RuntimeResult<ForallFact> {
        let flat: Vec<BoundName> = plain
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.clone())
            .collect();
        let n = flat.len();
        if n == 0 {
            return Err(RuntimeError::InternalBug(
                "exist! uniqueness: existential has no binders".to_string(),
            ));
        }

        let mut copy_a = Vec::with_capacity(n);
        let mut copy_b = Vec::with_capacity(n);
        for (i, binder) in flat.iter().enumerate() {
            copy_a.push(BoundName::new(
                self.global_ids.allocate_identifier_id(),
                format!("{}_a{i}", binder.name),
            ));
            copy_b.push(BoundName::new(
                self.global_ids.allocate_identifier_id(),
                format!("{}_b{i}", binder.name),
            ));
        }

        let mut map_a = HashMap::new();
        let mut map_b = HashMap::new();
        let mut forall_groups = Vec::new();

        let mut idx = 0usize;
        for group in &plain.typed_parameters.groups {
            let param_type = self
                .inst_param_type(&group.param_type, &map_a)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!(
                        "exist! uniqueness: instantiate type (copy a): {e}"
                    ))
                })?;
            let mut params = Vec::new();
            for old in &group.params {
                let fresh = copy_a[idx].clone();
                map_a.insert(
                    old.id,
                    Obj::Identifier(IdentifierObj::from_bound_name(&fresh)),
                );
                params.push(fresh);
                idx += 1;
            }
            forall_groups.push(TypedParameterGroup { params, param_type });
        }

        idx = 0;
        for group in &plain.typed_parameters.groups {
            let param_type = self
                .inst_param_type(&group.param_type, &map_b)
                .map_err(|e| {
                    RuntimeError::InternalBug(format!(
                        "exist! uniqueness: instantiate type (copy b): {e}"
                    ))
                })?;
            let mut params = Vec::new();
            for old in &group.params {
                let fresh = copy_b[idx].clone();
                map_b.insert(
                    old.id,
                    Obj::Identifier(IdentifierObj::from_bound_name(&fresh)),
                );
                params.push(fresh);
                idx += 1;
            }
            forall_groups.push(TypedParameterGroup { params, param_type });
        }

        let mut dom_facts = Vec::new();
        for body in &plain.facts {
            let inst_a = self.inst_quantifier_free_fact(body, &map_a).map_err(|e| {
                RuntimeError::InternalBug(format!(
                    "exist! uniqueness: instantiate body (copy a): {e}"
                ))
            })?;
            dom_facts.push(quantifier_free_fact_to_fact(inst_a));
            let inst_b = self.inst_quantifier_free_fact(body, &map_b).map_err(|e| {
                RuntimeError::InternalBug(format!(
                    "exist! uniqueness: instantiate body (copy b): {e}"
                ))
            })?;
            dom_facts.push(quantifier_free_fact_to_fact(inst_b));
        }

        let then_facts = if n == 1 || !component_conclusion {
            let left = witness_tuple_or_single(&copy_a);
            let right = witness_tuple_or_single(&copy_b);
            let equal = AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: plain.line_file.clone(),
            });
            vec![ExistOrAndChainAtomicFact::AtomicFact(equal)]
        } else {
            let mut equals = Vec::with_capacity(n);
            for (left_b, right_b) in copy_a.iter().zip(copy_b.iter()) {
                equals.push(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: Obj::Identifier(IdentifierObj::from_bound_name(left_b)),
                    right: Obj::Identifier(IdentifierObj::from_bound_name(right_b)),
                    line_file: plain.line_file.clone(),
                }));
            }
            vec![ExistOrAndChainAtomicFact::AndFact(AndFact {
                fact_id: self.global_ids.allocate_fact_id(),
                facts: equals,
                line_file: plain.line_file.clone(),
            })]
        };

        Ok(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: forall_groups,
            },
            dom_facts,
            then_facts,
            line_file: plain.line_file.clone(),
        })
    }
}

fn witness_tuple_or_single(binders: &[BoundName]) -> Obj {
    if binders.len() == 1 {
        Obj::Identifier(IdentifierObj::from_bound_name(&binders[0]))
    } else {
        Obj::ProductShape(ProductShape::Tuple(Tuple {
            args: binders
                .iter()
                .map(|b| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(b))))
                .collect(),
        }))
    }
}
