use crate::ast::fact::{
    negate_atomic_fact, AndChainAtomicFact, AndFact, AtomicFact, OrFact, QuantifierFreeFact,
};
use crate::ast::line_file::SourceLine;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(crate) fn disjoin_quantifier_free_facts(
        &mut self,
        facts: &[QuantifierFreeFact],
        line_file: Option<SourceLine>,
    ) -> RuntimeResult<Option<QuantifierFreeFact>> {
        let mut terms = Vec::new();
        for fact in facts {
            let Some(alternatives) = self.quantifier_free_to_dnf(fact)? else {
                return Ok(None);
            };
            terms.extend(alternatives);
        }
        Ok(self.quantifier_free_from_dnf(terms, line_file))
    }

    fn quantifier_free_to_dnf(
        &mut self,
        fact: &QuantifierFreeFact,
    ) -> RuntimeResult<Option<Vec<Vec<AtomicFact>>>> {
        let terms = match fact {
            QuantifierFreeFact::AtomicFact(a) => vec![vec![a.clone()]],
            QuantifierFreeFact::AndFact(a) => vec![a.facts.clone()],
            QuantifierFreeFact::ChainFact(c) => vec![self.chain_adjacent_atomics(c)?],
            QuantifierFreeFact::OrFact(o) => {
                let mut terms = Vec::new();
                for branch in &o.facts {
                    terms.push(match branch {
                        AndChainAtomicFact::AtomicFact(a) => vec![a.clone()],
                        AndChainAtomicFact::AndFact(a) => a.facts.clone(),
                        AndChainAtomicFact::ChainFact(c) => self.chain_adjacent_atomics(c)?,
                    });
                }
                terms
            }
        };
        if terms.is_empty() || terms.iter().any(Vec::is_empty) {
            return Ok(None);
        }
        Ok(Some(terms))
    }

    // Negate each conjunct directly into DNF and join the alternatives.
    // Avoid a whole-formula CNF -> DNF roundtrip, which can grow needlessly.
    pub(crate) fn negate_quantifier_free_conjunction(
        &mut self,
        facts: &[QuantifierFreeFact],
        line_file: Option<SourceLine>,
    ) -> RuntimeResult<Option<QuantifierFreeFact>> {
        let mut terms = Vec::new();
        for fact in facts {
            let Some(cnf) = self.negate_quantifier_free_to_cnf(fact)? else {
                return Ok(None);
            };
            terms.extend(cnf_to_dnf(&cnf));
        }
        Ok(self.quantifier_free_from_dnf(terms, line_file))
    }

    // Existential bodies already conjoin QF facts. Choose the smaller literal
    // footprint without changing the formula; ties retain the legacy CNF shape.
    pub(crate) fn negate_quantifier_free_conjunction_to_conjuncts(
        &mut self,
        facts: &[QuantifierFreeFact],
        line_file: Option<SourceLine>,
    ) -> RuntimeResult<Option<Vec<QuantifierFreeFact>>> {
        if facts.is_empty() {
            return Ok(None);
        }
        let mut parts = Vec::new();
        let mut cnf_count = 1usize;
        let mut cnf_atoms = 0usize;
        let mut dnf_atoms = 0usize;
        for fact in facts {
            let Some(cnf) = self.negate_quantifier_free_to_cnf(fact)? else {
                return Ok(None);
            };
            let count = cnf.len();
            let atoms = cnf
                .iter()
                .fold(0usize, |n, clause| n.saturating_add(clause.len()));
            cnf_atoms = cnf_atoms
                .saturating_mul(count)
                .saturating_add(atoms.saturating_mul(cnf_count));
            cnf_count = cnf_count.saturating_mul(count);
            let terms = cnf
                .iter()
                .fold(1usize, |n, clause| n.saturating_mul(clause.len()));
            dnf_atoms = dnf_atoms.saturating_add(terms.saturating_mul(count));
            parts.push(cnf);
        }
        if dnf_atoms < cnf_atoms {
            let mut terms = Vec::new();
            for part in parts {
                terms.extend(cnf_to_dnf(&part));
            }
            return Ok(self
                .quantifier_free_from_dnf(terms, line_file)
                .map(|fact| vec![fact]));
        }
        let mut combined = parts.remove(0);
        for part in parts {
            combined = disjoin_cnfs(&combined, &part);
        }
        let mut conjuncts = Vec::new();
        for clause in combined {
            let terms = clause.into_iter().map(|atom| vec![atom]).collect();
            let Some(fact) = self.quantifier_free_from_dnf(terms, line_file.clone()) else {
                return Ok(None);
            };
            conjuncts.push(fact);
        }
        Ok(Some(conjuncts))
    }

    // Every existing QF node is DNF. Its negation is one CNF clause per branch.
    fn negate_quantifier_free_to_cnf(
        &mut self,
        fact: &QuantifierFreeFact,
    ) -> RuntimeResult<Option<Vec<Vec<AtomicFact>>>> {
        let Some(terms) = self.quantifier_free_to_dnf(fact)? else {
            return Ok(None);
        };
        let mut clauses = Vec::new();
        for atoms in terms {
            let Some(clause) = self.negate_atomics(&atoms) else {
                return Ok(None);
            };
            clauses.push(clause);
        }
        Ok(Some(clauses))
    }

    fn negate_atomics(&mut self, atoms: &[AtomicFact]) -> Option<Vec<AtomicFact>> {
        if atoms.is_empty() {
            return None;
        }
        let mut negated = Vec::with_capacity(atoms.len());
        for atom in atoms {
            negated.push(negate_atomic_fact(
                atom,
                self.global_ids.allocate_fact_id(),
            )?);
        }
        Some(negated)
    }

    fn quantifier_free_from_dnf(
        &mut self,
        terms: Vec<Vec<AtomicFact>>,
        line_file: Option<SourceLine>,
    ) -> Option<QuantifierFreeFact> {
        let mut branches = Vec::with_capacity(terms.len());
        for mut atoms in terms {
            if atoms.is_empty() {
                return None;
            }
            let branch = if atoms.len() == 1 {
                AndChainAtomicFact::AtomicFact(atoms.remove(0))
            } else {
                AndChainAtomicFact::AndFact(AndFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    facts: atoms,
                    line_file: line_file.clone(),
                })
            };
            branches.push(branch);
        }
        if branches.len() == 1 {
            return Some(match branches.remove(0) {
                AndChainAtomicFact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => QuantifierFreeFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => QuantifierFreeFact::ChainFact(c),
            });
        }
        if branches.is_empty() {
            return None;
        }
        Some(QuantifierFreeFact::OrFact(OrFact {
            fact_id: self.global_ids.allocate_fact_id(),
            facts: branches,
            line_file,
        }))
    }
}

fn cnf_to_dnf(clauses: &[Vec<AtomicFact>]) -> Vec<Vec<AtomicFact>> {
    let mut terms = vec![Vec::new()];
    for clause in clauses {
        let mut next = Vec::new();
        for term in &terms {
            for atom in clause {
                let mut extended = term.clone();
                extended.push(atom.clone());
                next.push(extended);
            }
        }
        terms = next;
    }
    terms
}

fn disjoin_cnfs(left: &[Vec<AtomicFact>], right: &[Vec<AtomicFact>]) -> Vec<Vec<AtomicFact>> {
    let mut clauses = Vec::new();
    for a in left {
        for b in right {
            let mut clause = a.clone();
            clause.extend(b.iter().cloned());
            clauses.push(clause);
        }
    }
    clauses
}
