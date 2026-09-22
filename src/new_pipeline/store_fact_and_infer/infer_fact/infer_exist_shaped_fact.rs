use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    exist_shaped_fact_from_fact, negate_atomic_fact, AndChainAtomicFact, ExistOrAndChainAtomicFact,
    ExistShapedFact, Fact, ForallFact, OrFact, PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::ast::param::{TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferExistShapedFactResult, InferExistUniqueFactResult, InferExistUniqueUniquenessForallResult,
    InferNotExistDemorganForallResult, InferNotExistFactResult, InferPlainExistFactResult,
};

impl Runtime {
    // Exist family infer by shape tag.
    // - plain `exist`: NoInfer
    // - `exist!`: store uniqueness forall (componentwise when multi-binder)
    // - `not exist`: store De Morgan forall when body shape is supported
    pub(crate) fn infer_exist_shaped_fact(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<InferExistShapedFactResult> {
        let Some(family) = exist_shaped_fact_from_fact(fact) else {
            return Err(crate::new_pipeline::runtime::RuntimeError::InternalBug(
                "infer_exist_shaped_fact: expected exist-shaped fact".to_string(),
            ));
        };
        match family {
            ExistShapedFact::Exist(_) => Ok(InferExistShapedFactResult::Exist(
                InferPlainExistFactResult::NoInfer,
            )),
            ExistShapedFact::ExistUnique(plain) => Ok(InferExistShapedFactResult::ExistUnique(
                self.infer_exist_unique_fact(&plain)?,
            )),
            ExistShapedFact::NotExist(plain) => Ok(InferExistShapedFactResult::NotExist(
                self.infer_not_exist_fact(&plain)?,
            )),
        }
    }

    // When: stored `exist! xs st {body}` with at least one binder.
    // Infers: uniqueness forall over two witness copies (Manual Builtin Inference).
    // Example: trust `exist! x R st {x = 0}` also stores the uniqueness forall.
    fn infer_exist_unique_fact(
        &mut self,
        plain: &PlainExistFact,
    ) -> RuntimeResult<InferExistUniqueFactResult> {
        let n: usize = plain
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum();
        if n == 0 {
            return Ok(InferExistUniqueFactResult::NoInfer);
        }
        let uniqueness = self.build_exist_unique_component_uniqueness_forall_fact(plain)?;
        let derived = Box::new(
            self.store_inferred_fact_and_infer(&Fact::ForallFact(uniqueness))?,
        );
        Ok(InferExistUniqueFactResult::UniquenessForall(
            InferExistUniqueUniquenessForallResult { derived },
        ))
    }

    // When: stored `not exist xs st {body}` with binders; body has no `or` conjunct.
    // Infers: forall xs: (De Morgan of body) when negation is supported.
    // Example: trust `not exist x R st {x > 0}` also stores `forall x R: not x > 0`.
    fn infer_not_exist_fact(
        &mut self,
        plain: &PlainExistFact,
    ) -> RuntimeResult<InferNotExistFactResult> {
        let Some(forall) = self.not_exist_to_demorgan_forall(plain)? else {
            return Ok(InferNotExistFactResult::NoInfer);
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::ForallFact(forall))?);
        Ok(InferNotExistFactResult::DemorganForall(
            InferNotExistDemorganForallResult { derived },
        ))
    }

    // not exist xs st {c1, c2, …} → forall xs: ¬c1 or ¬c2 or …
    // None when no binders, empty body, `or` in a conjunct, or an atom cannot be negated.
    fn not_exist_to_demorgan_forall(
        &mut self,
        plain: &PlainExistFact,
    ) -> RuntimeResult<Option<ForallFact>> {
        let n: usize = plain
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum();
        if n == 0 || plain.facts.is_empty() {
            return Ok(None);
        }

        let flat: Vec<BoundName> = plain
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.clone())
            .collect();
        let mut fresh = Vec::with_capacity(flat.len());
        for (i, binder) in flat.iter().enumerate() {
            fresh.push(BoundName::new(
                self.ids.allocate_identifier_id(),
                format!("{}_ne{i}", binder.name),
            ));
        }

        let mut subst = HashMap::new();
        let mut forall_groups = Vec::new();
        let mut idx = 0usize;
        for group in &plain.typed_parameters.groups {
            let param_type = self.inst_param_type(&group.param_type, &subst).map_err(|e| {
                crate::new_pipeline::runtime::RuntimeError::InternalBug(format!(
                    "not exist demorgan: instantiate type: {e}"
                ))
            })?;
            let mut params = Vec::new();
            for old in &group.params {
                let b = fresh[idx].clone();
                subst.insert(old.id, Obj::Identifier(IdentifierObj::from_bound_name(&b)));
                params.push(b);
                idx += 1;
            }
            forall_groups.push(TypedParameterGroup { params, param_type });
        }

        let mut disjuncts: Vec<AndChainAtomicFact> = Vec::new();
        for body in &plain.facts {
            let inst = self.inst_quantifier_free_fact(body, &subst).map_err(|e| {
                crate::new_pipeline::runtime::RuntimeError::InternalBug(format!(
                    "not exist demorgan: instantiate body: {e}"
                ))
            })?;
            let Some(part) = self.demorgan_negate_exist_body_conjunct_to_disjuncts(&inst)? else {
                return Ok(None);
            };
            disjuncts.extend(part);
        }
        if disjuncts.is_empty() {
            return Ok(None);
        }

        let then_fact = if disjuncts.len() == 1 {
            match disjuncts.pop().expect("one disjunct") {
                AndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            }
        } else {
            ExistOrAndChainAtomicFact::OrFact(OrFact {
                fact_id: self.ids.allocate_fact_id(),
                facts: disjuncts,
                line_file: plain.line_file.clone(),
            })
        };

        Ok(Some(ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: forall_groups,
            },
            dom_facts: Vec::<Fact>::new(),
            then_facts: vec![then_fact],
            line_file: plain.line_file.clone(),
        }))
    }

    // Same shape limits as legacy: atomic / and / chain ok; `or` conjunct unsupported.
    fn demorgan_negate_exist_body_conjunct_to_disjuncts(
        &mut self,
        conjunct: &QuantifierFreeFact,
    ) -> RuntimeResult<Option<Vec<AndChainAtomicFact>>> {
        match conjunct {
            QuantifierFreeFact::AtomicFact(a) => {
                let Some(neg) = negate_atomic_fact(a, self.ids.allocate_fact_id()) else {
                    return Ok(None);
                };
                Ok(Some(vec![AndChainAtomicFact::AtomicFact(neg)]))
            }
            QuantifierFreeFact::AndFact(af) => {
                if af.facts.is_empty() {
                    return Ok(None);
                }
                let mut out = Vec::with_capacity(af.facts.len());
                for a in &af.facts {
                    let Some(neg) = negate_atomic_fact(a, self.ids.allocate_fact_id()) else {
                        return Ok(None);
                    };
                    out.push(AndChainAtomicFact::AtomicFact(neg));
                }
                Ok(Some(out))
            }
            QuantifierFreeFact::ChainFact(c) => {
                let adjacent = self.chain_adjacent_atomics(c)?;
                if adjacent.is_empty() {
                    return Ok(None);
                }
                let mut out = Vec::with_capacity(adjacent.len());
                for a in &adjacent {
                    let Some(neg) = negate_atomic_fact(a, self.ids.allocate_fact_id()) else {
                        return Ok(None);
                    };
                    out.push(AndChainAtomicFact::AtomicFact(neg));
                }
                Ok(Some(out))
            }
            QuantifierFreeFact::OrFact(_) => Ok(None),
        }
    }
}
