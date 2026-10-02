use crate::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact, NormalAtomicFact,
};
use crate::ast::param::{ParamType, TypedParameterList};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::helper::flatten_def_prop_params;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferExpandDefinitionResult,
    InferNormalAtomicParamTypesProjectedResult,
};

impl Runtime {
    // Additive NormalAtomic rules: param-type projection, then iff expand.
    pub(super) fn infer_normal_atomic_fact_rules(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(param_types) = self.infer_normal_atomic_param_types(normal)? {
            rules.push(InferAtomicExceptEqualityResult::NormalAtomicParamTypes(
                param_types,
            ));
        }
        if let Some(expand) = self.infer_normal_atomic_expand_definition(normal)? {
            rules.push(InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(
                expand,
            ));
        }
        Ok(rules)
    }

    // When: stored `$P(args)` and `P` is a concrete prop.
    // Infers: each argument's type obligation (`x $in S`, `$is_set(A)`, …),
    // with `S` instantiated by the call-site args (not the prop binder names).
    // Example:
    //   prop P(A nonempty_set, one A): …
    //   $P(Carrier, one)  ⇒  infer `one $in Carrier` (not `one $in A`)
    fn infer_normal_atomic_param_types(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<Option<InferNormalAtomicParamTypesProjectedResult>> {
        if self.def_abstract_prop_visible(&normal.predicate).is_some() {
            return Ok(None);
        }
        let Some(definition) = self.def_prop_visible(&normal.predicate) else {
            return Ok(None);
        };
        let definition = definition.clone();
        let flat = flatten_typed_param_types(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(None);
        }
        let mut subst = std::collections::HashMap::new();
        for ((param, _), arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
        }
        let mut derived = Vec::new();
        for ((_param, param_type), arg) in flat.iter().zip(normal.body.iter()) {
            let Ok(inst_type) = self.inst_param_type(param_type, &subst) else {
                continue;
            };
            let Some(obligation) =
                type_obligation_fact(arg, &inst_type, &mut self.global_ids)
            else {
                continue;
            };
            derived.push(self.store_inferred_fact_and_infer(&obligation)?);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferNormalAtomicParamTypesProjectedResult { derived }))
    }

    // When: stored `$P(args)` and `P` is a concrete prop with iff facts.
    // Infers: each instantiated iff fact (one layer).
    fn infer_normal_atomic_expand_definition(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<Option<InferExpandDefinitionResult>> {
        if self.def_abstract_prop_visible(&normal.predicate).is_some() {
            return Ok(None);
        }
        let Some(definition) = self.def_prop_visible(&normal.predicate) else {
            return Ok(None);
        };
        if definition.iff_facts.is_empty() {
            return Ok(None);
        }
        let definition = definition.clone();
        let flat = flatten_def_prop_params(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(None);
        }
        let mut subst = std::collections::HashMap::new();
        for (param, arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
        }
        let mut derived = Vec::new();
        for iff_fact in &definition.iff_facts {
            let Ok(instantiated) = self.inst_fact(iff_fact, &subst) else {
                continue;
            };
            derived.push(self.store_inferred_fact_and_infer(&instantiated)?);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferExpandDefinitionResult { derived }))
    }
}

fn flatten_typed_param_types(
    list: &TypedParameterList,
) -> Vec<(
    crate::ast::names::BoundName,
    ParamType,
)> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push((param.clone(), group.param_type.clone()));
        }
    }
    out
}

fn type_obligation_fact(
    arg: &crate::ast::obj::Obj,
    param_type: &ParamType,
    global_ids: &mut crate::runtime::GlobalIds,
) -> Option<Fact> {
    let fact_id = global_ids.allocate_fact_id();
    match param_type {
        ParamType::Obj(set) => Some(Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id,
            element: arg.clone(),
            set: set.clone(),
            line_file: None,
        }))),
        ParamType::Set(_) => Some(Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: arg.clone(),
            line_file: None,
        }))),
        ParamType::NonemptySet(_) => Some(Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
            IsNonemptySetFact {
                fact_id,
                set: arg.clone(),
                line_file: None,
            },
        ))),
        ParamType::FiniteSet(_) => Some(Fact::AtomicFact(AtomicFact::IsFiniteSetFact(
            IsFiniteSetFact {
                fact_id,
                set: arg.clone(),
                line_file: None,
            },
        ))),
    }
}
