//! Finite cardinality consequences consume existing map certificates only.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InjectiveFact};
use crate::ast::obj::{FiniteSetStat, FunctionSpace, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::runtime::Runtime;

pub enum FiniteMapSizeProof {
    Bijective {
        certificate: AtomicExceptEqualityFactKnownProof,
    },
    InjectiveRange {
        certificate: AtomicExceptEqualityFactKnownProof,
    },
}
impl FiniteMapSizeProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::Bijective { .. } => "FiniteBijectiveSize",
            Self::InjectiveRange { .. } => "FiniteInjectiveRangeSize",
        }
    }
    pub fn certificate(&self) -> &AtomicExceptEqualityFactKnownProof {
        match self {
            Self::Bijective { certificate } | Self::InjectiveRange { certificate } => certificate,
        }
    }
}
impl Runtime {
    pub(super) fn search_finite_map_size(
        &mut self,
        fact: &EqualFact,
    ) -> Option<FiniteMapSizeProof> {
        let (Some(left), Some(right)) = (size_set(&fact.left), size_set(&fact.right)) else {
            return None;
        };
        // Both sizes have passed their finite-set WD. A stored bijection
        // between exactly these carriers therefore preserves cardinality.
        let candidates: Vec<_> = self
            .execution_environments_stack
            .iter()
            .rev()
            .flat_map(|env| env.facts.facts_by_id.values())
            .filter_map(|fact| match fact {
                Fact::AtomicFact(AtomicFact::BijectiveFact(b)) => Some(b.clone()),
                _ => None,
            })
            .collect();
        for candidate in candidates {
            if (candidate.domain.ir() == left.ir() && candidate.codomain.ir() == right.ir())
                || (candidate.domain.ir() == right.ir() && candidate.codomain.ir() == left.ir())
            {
                if let Some(certificate) =
                    self.lookup_known_atomic_premise(AtomicFact::BijectiveFact(candidate))
                {
                    return Some(FiniteMapSizeProof::Bijective { certificate });
                }
            }
        }
        // The range of a unary injection contains one value per source point.
        for (range, source) in [(left, right), (right, left)] {
            let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = range else {
                continue;
            };
            let Some(signature) = self.resolve_callable_fn_set(&range.function) else {
                continue;
            };
            let count: usize = signature
                .set_bound_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum();
            if count != 1
                || signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .any(|g| !g.params.is_empty() && g.param_type.ir() != source.ir())
            {
                continue;
            }
            let certificate = AtomicFact::InjectiveFact(InjectiveFact {
                fact_id: self.global_ids.allocate_fact_id(),
                domain: source.clone(),
                codomain: *signature.ret_set.clone(),
                function: *range.function.clone(),
                line_file: None,
            });
            if let Some(certificate) = self.lookup_known_atomic_premise(certificate) {
                return Some(FiniteMapSizeProof::InjectiveRange { certificate });
            }
        }
        None
    }
}
fn size_set(o: &Obj) -> Option<&Obj> {
    match o {
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(s)) => Some(&s.set),
        _ => None,
    }
}
