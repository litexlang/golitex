//! `have Img set by replacement_axiom(P, A)` — named Replacement image.
//!
//! No anonymous `replacement_image` Obj. After uniqueness of `P` on `A` is
//! known, introduce `Img` as a set and store intro/elim facts.

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, NormalAtomicFact,
    PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::ast::param::{
    ParamType, Set, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::HaveByReplacementAxiomStmt;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveByReplacementAxiomStmtFailed {
    PropArity(String),
    SourceWd(VerifyObjWellDefinedResult),
    UniquenessMissing(String),
    Define(String),
}

pub struct ExecHaveByReplacementAxiomStmtSuccessResult {
    pub statement: HaveByReplacementAxiomStmt,
    pub source_wd: VerifyObjWellDefinedResult,
    pub stored_fact_ids: Vec<crate::new_pipeline::runtime::FactId>,
}

pub enum ExecHaveByReplacementAxiomStmtResult {
    Success(ExecHaveByReplacementAxiomStmtSuccessResult),
    Failed(ExecHaveByReplacementAxiomStmtFailed),
}

impl ExecHaveByReplacementAxiomStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Example:
    //   have Img set by replacement_axiom(image_rel, {1, 2})
    pub(super) fn exec_have_by_replacement_axiom_stmt(
        &mut self,
        stmt: &HaveByReplacementAxiomStmt,
    ) -> RuntimeResult<ExecHaveByReplacementAxiomStmtResult> {
        let prop_ir = stmt.prop_name.display_string();
        let source_ir = stmt.source_set.ir();

        let arity = match self.replacement_prop_arity(&stmt.prop_name) {
            Ok(n) => n,
            Err(msg) => {
                return Ok(ExecHaveByReplacementAxiomStmtResult::Failed(
                    ExecHaveByReplacementAxiomStmtFailed::PropArity(msg),
                ));
            }
        };
        if arity != 2 {
            return Ok(ExecHaveByReplacementAxiomStmtResult::Failed(
                ExecHaveByReplacementAxiomStmtFailed::PropArity(format!(
                    "replacement_axiom({prop_ir}, {source_ir}) expects a binary prop, but `{prop_ir}` has arity {arity}"
                )),
            ));
        }

        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };
        let source_wd =
            self.verify_obj_well_definedness(&stmt.source_set, verify_state.clone())?;
        if source_wd.is_failed() {
            return Ok(ExecHaveByReplacementAxiomStmtResult::Failed(
                ExecHaveByReplacementAxiomStmtFailed::SourceWd(source_wd),
            ));
        }

        if !self.known_replacement_uniqueness(&stmt.prop_name, &stmt.source_set) {
            return Ok(ExecHaveByReplacementAxiomStmtResult::Failed(
                ExecHaveByReplacementAxiomStmtFailed::UniquenessMissing(format!(
                    "replacement_axiom({prop_ir}, {source_ir}) needs uniqueness of `{prop_ir}` over `{source_ir}`: forall x {source_ir}, y, y2 set: ${prop_ir}(x, y) ${prop_ir}(x, y2) => y = y2"
                )),
            ));
        }

        let param_def = TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![stmt.name.clone()],
                param_type: ParamType::Set(Set {}),
            }],
        };
        let store = self.define_typed_parameters_in_current_env(
            &param_def,
            Some(SharedHaveDefinition::HaveByReplacementAxiom(Rc::new(
                stmt.clone(),
            ))),
        );
        let store = match store {
            Ok(s) => s,
            Err(e) => {
                return Ok(ExecHaveByReplacementAxiomStmtResult::Failed(
                    ExecHaveByReplacementAxiomStmtFailed::Define(format!("{e:?}")),
                ));
            }
        };

        let img = Obj::Identifier(IdentifierObj::from_bound_name(&stmt.name));
        let intro = self.replacement_intro_forall(stmt, &img);
        let elim = self.replacement_elim_forall(stmt, &img);
        let mut stored_fact_ids = store.stored_fact_ids;
        stored_fact_ids.extend(
            self.store_fact_and_infer(&Fact::ForallFact(intro))?
                .stored_fact_ids(),
        );
        stored_fact_ids.extend(
            self.store_fact_and_infer(&Fact::ForallFact(elim))?
                .stored_fact_ids(),
        );

        Ok(ExecHaveByReplacementAxiomStmtResult::Success(
            ExecHaveByReplacementAxiomStmtSuccessResult {
                statement: stmt.clone(),
                source_wd,
                stored_fact_ids,
            },
        ))
    }

    fn replacement_prop_arity(&self, prop_name: &AtomicName) -> Result<usize, String> {
        if let Some(definition) = self.def_prop_visible(prop_name) {
            return Ok(definition.typed_parameters.ordered_param_ids().len());
        }
        if let Some(definition) = self.def_abstract_prop_visible(prop_name) {
            return Ok(definition.params.len());
        }
        Err(format!(
            "replacement_axiom expects `{}` to be a user-defined prop or abstract_prop",
            prop_name.display_string()
        ))
    }

    fn known_replacement_uniqueness(&self, prop_name: &AtomicName, source_set: &Obj) -> bool {
        for env in self.execution_environments_stack.iter().rev() {
            for cite in &env.facts.known_forall_conclusions.equal_conclusions {
                let Some(Fact::ForallFact(forall)) = env.facts.facts_by_id.get(&cite.fact_id) else {
                    continue;
                };
                if forall_is_replacement_uniqueness(forall, prop_name, source_set) {
                    return true;
                }
            }
        }
        false
    }

    // forall x A, y set: $P(x,y) => y $in Img
    pub(crate) fn replacement_intro_forall(
        &mut self,
        stmt: &HaveByReplacementAxiomStmt,
        img: &Obj,
    ) -> ForallFact {
        let x = self.fresh_internal_param();
        let y = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
        let line = Some(stmt.line_file.clone());
        ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![
                    TypedParameterGroup {
                        params: vec![x],
                        param_type: ParamType::Obj(stmt.source_set.clone()),
                    },
                    TypedParameterGroup {
                        params: vec![y],
                        param_type: ParamType::Set(Set {}),
                    },
                ],
            },
            dom_facts: vec![Fact::AtomicFact(AtomicFact::NormalAtomicFact(
                NormalAtomicFact {
                    fact_id: self.ids.allocate_fact_id(),
                    predicate: stmt.prop_name.clone(),
                    body: vec![x_obj, y_obj.clone()],
                    line_file: line.clone(),
                },
            ))],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.ids.allocate_fact_id(),
                    element: y_obj,
                    set: img.clone(),
                    line_file: line.clone(),
                },
            ))],
            line_file: line,
        }
    }

    // forall y Img: exist x A st {$P(x,y)}
    pub(crate) fn replacement_elim_forall(
        &mut self,
        stmt: &HaveByReplacementAxiomStmt,
        img: &Obj,
    ) -> ForallFact {
        let y = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let line = Some(stmt.line_file.clone());
        ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![y],
                    param_type: ParamType::Obj(img.clone()),
                }],
            },
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(PlainExistFact {
                fact_id: self.ids.allocate_fact_id(),
                typed_parameters: TypedParameterList {
                    groups: vec![TypedParameterGroup {
                        params: vec![x],
                        param_type: ParamType::Obj(stmt.source_set.clone()),
                    }],
                },
                facts: vec![QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(
                    NormalAtomicFact {
                        fact_id: self.ids.allocate_fact_id(),
                        predicate: stmt.prop_name.clone(),
                        body: vec![x_obj, y_obj],
                        line_file: line.clone(),
                    },
                ))],
                line_file: line.clone(),
            })],
            line_file: line,
        }
    }
}

fn forall_is_replacement_uniqueness(
    forall: &ForallFact,
    prop_name: &AtomicName,
    source_set: &Obj,
) -> bool {
    let mut x_id: Option<IdentifierId> = None;
    let mut y_id: Option<IdentifierId> = None;
    let mut y2_id: Option<IdentifierId> = None;
    for group in &forall.typed_parameters.groups {
        for param in &group.params {
            match &group.param_type {
                ParamType::Obj(domain) if x_id.is_none() && domain == source_set => {
                    x_id = Some(param.id);
                }
                ParamType::Set(_) if y_id.is_none() => {
                    y_id = Some(param.id);
                }
                ParamType::Set(_) if y2_id.is_none() => {
                    y2_id = Some(param.id);
                }
                _ => return false,
            }
        }
    }
    let (Some(x_id), Some(y_id), Some(y2_id)) = (x_id, y_id, y2_id) else {
        return false;
    };
    let param_count: usize = forall
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum();
    if param_count != 3 {
        return false;
    }
    if forall.dom_facts.len() != 2 || forall.then_facts.len() != 1 {
        return false;
    }
    let mut saw_p_x_y = false;
    let mut saw_p_x_y2 = false;
    for dom in &forall.dom_facts {
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(normal)) = dom else {
            return false;
        };
        if &normal.predicate != prop_name || normal.body.len() != 2 {
            return false;
        }
        if !obj_is_bound_param(&normal.body[0], x_id) {
            return false;
        }
        if obj_is_bound_param(&normal.body[1], y_id) {
            saw_p_x_y = true;
        } else if obj_is_bound_param(&normal.body[1], y2_id) {
            saw_p_x_y2 = true;
        } else {
            return false;
        }
    }
    if !saw_p_x_y || !saw_p_x_y2 {
        return false;
    }
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        left,
        right,
        ..
    })) = &forall.then_facts[0]
    else {
        return false;
    };
    (obj_is_bound_param(left, y_id) && obj_is_bound_param(right, y2_id))
        || (obj_is_bound_param(left, y2_id) && obj_is_bound_param(right, y_id))
}

fn obj_is_bound_param(obj: &Obj, id: IdentifierId) -> bool {
    matches!(
        obj,
        Obj::Identifier(IdentifierObj::Plain { id: plain, .. }) if *plain == id
    )
}
