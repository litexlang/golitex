use crate::ast::fact::{
    negate_atomic_fact, AndChainAtomicFact, AtomicFact, ExistShapedFact, NotForallFact, OrFact,
    PlainExistFact, QuantifierFreeFact,
};
use crate::ast::line_file::SourceLine;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // not forall → exist binders st { dom…, not(then)… }.
    // None when some then-clause cannot be negated (e.g. FnEqual* has no not-form).
    pub(crate) fn not_forall_to_counterexample_exist(
        &mut self,
        not_forall: &NotForallFact,
    ) -> RuntimeResult<Option<ExistShapedFact>> {
        let mut body: Vec<QuantifierFreeFact> = not_forall.dom_facts.clone();
        for then in &not_forall.then_facts {
            let Some(conjuncts) = self.negate_quantifier_free_to_conjuncts(then)? else {
                return Ok(None);
            };
            for c in conjuncts {
                body.push(collapse_single_branch_or(c));
            }
        }
        if body.is_empty() {
            return Ok(None);
        }
        Ok(Some(ExistShapedFact::Exist(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: not_forall.typed_parameters.clone(),
            facts: body,
            line_file: not_forall.line_file.clone(),
        })))
    }

    // De Morgan into exist-body conjuncts (exist body = conjunction of QF facts).
    fn negate_quantifier_free_to_conjuncts(
        &mut self,
        fact: &QuantifierFreeFact,
    ) -> RuntimeResult<Option<Vec<QuantifierFreeFact>>> {
        match fact {
            QuantifierFreeFact::AtomicFact(a) => {
                let Some(neg) = negate_atomic_fact(a, self.global_ids.allocate_fact_id()) else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::AtomicFact(neg)]))
            }
            QuantifierFreeFact::AndFact(a) => {
                let Some(or_fact) = self.negate_atomics_to_or(&a.facts, a.line_file.clone())? else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::OrFact(or_fact)]))
            }
            QuantifierFreeFact::OrFact(o) => {
                let mut out = Vec::new();
                for branch in &o.facts {
                    let Some(part) = self.negate_and_chain_branch_to_conjuncts(branch)? else {
                        return Ok(None);
                    };
                    out.extend(part);
                }
                Ok(Some(out))
            }
            QuantifierFreeFact::ChainFact(c) => {
                let adjacent = self.chain_adjacent_atomics(c)?;
                let Some(or_fact) = self.negate_atomics_to_or(&adjacent, c.line_file.clone())? else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::OrFact(or_fact)]))
            }
        }
    }

    fn negate_and_chain_branch_to_conjuncts(
        &mut self,
        branch: &AndChainAtomicFact,
    ) -> RuntimeResult<Option<Vec<QuantifierFreeFact>>> {
        match branch {
            AndChainAtomicFact::AtomicFact(a) => {
                let Some(neg) = negate_atomic_fact(a, self.global_ids.allocate_fact_id()) else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::AtomicFact(neg)]))
            }
            AndChainAtomicFact::AndFact(a) => {
                let Some(or_fact) = self.negate_atomics_to_or(&a.facts, a.line_file.clone())? else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::OrFact(or_fact)]))
            }
            AndChainAtomicFact::ChainFact(c) => {
                let adjacent = self.chain_adjacent_atomics(c)?;
                let Some(or_fact) = self.negate_atomics_to_or(&adjacent, c.line_file.clone())? else {
                    return Ok(None);
                };
                Ok(Some(vec![QuantifierFreeFact::OrFact(or_fact)]))
            }
        }
    }

    // not(A and B and …) → (not A) or (not B) or …
    fn negate_atomics_to_or(
        &mut self,
        atomics: &[AtomicFact],
        line_file: Option<SourceLine>,
    ) -> RuntimeResult<Option<OrFact>> {
        if atomics.is_empty() {
            return Ok(None);
        }
        let mut branches = Vec::with_capacity(atomics.len());
        for a in atomics {
            let Some(neg) = negate_atomic_fact(a, self.global_ids.allocate_fact_id()) else {
                return Ok(None);
            };
            branches.push(AndChainAtomicFact::AtomicFact(neg));
        }
        Ok(Some(OrFact {
            fact_id: self.global_ids.allocate_fact_id(),
            facts: branches,
            line_file,
        }))
    }
}

fn collapse_single_branch_or(qf: QuantifierFreeFact) -> QuantifierFreeFact {
    match qf {
        QuantifierFreeFact::OrFact(mut o) if o.facts.len() == 1 => {
            match o.facts.pop() {
                Some(AndChainAtomicFact::AtomicFact(a)) => QuantifierFreeFact::AtomicFact(a),
                Some(AndChainAtomicFact::AndFact(a)) => QuantifierFreeFact::AndFact(a),
                Some(AndChainAtomicFact::ChainFact(c)) => QuantifierFreeFact::ChainFact(c),
                None => QuantifierFreeFact::OrFact(o),
            }
        }
        other => other,
    }
}
