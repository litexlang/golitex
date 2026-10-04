use super::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
use super::closed_calculation_proof::{ClosedAtomicExceptEqualityCalculationProof, ClosedCalculationProof};
use super::structural_membership_proof::{IntrinsicCodomain, StructuralMembershipProof, StructuralMembershipReason};
use super::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::proper_subsets_in_membership_proof_order;
use super::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq;
use super::AtomicExceptEqualityFactSearchProofByKnownAtomicFact;
use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::obj::*;
use crate::runtime::Runtime;

impl Runtime {
    // Truth only, after WD. Recursion strictly removes an AST constructor.
    // Leaves cite stored facts or calculate closed values; never call the
    // verifier, atomic search, SP, definition unfolding or a rule dispatcher.
    pub(in crate::execute) fn search_structural_membership(
        &mut self,
        element: &Obj,
        target: &StandardSet,
    ) -> Option<StructuralMembershipProof> {
        use StandardSet::*;
        use StructuralMembershipReason as P;
        let goal = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: Obj::StandardSet(target.clone()),
            line_file: None,
        });
        if let Some(known) = self.lookup_known_atomic_fact(&goal) {
            return Some(StructuralMembershipProof::new(
                element.clone(),
                target.clone(),
                P::Known(known),
            ));
        }
        if let Some(ClosedCalculationProof::AtomicExceptEquality(
            ClosedAtomicExceptEqualityCalculationProof::In(proof),
        )) = calculate_closed_atomic_fact(&goal)
        {
            return Some(StructuralMembershipProof::new(
                element.clone(),
                target.clone(),
                P::Closed(proof),
            ));
        }
        // A finite standard-set table, with raw known lookup only. Do not call
        // the SP numeric-superset route from Direct, or recurse on another set.
        if let Some((source, known)) = self.lookup_structural_numeric_subset(&goal, element, target)
        {
            let source_proof =
                StructuralMembershipProof::new(element.clone(), source, P::Known(known));
            return Some(StructuralMembershipProof::new(
                element.clone(),
                target.clone(),
                P::StandardSuperset(Box::new(source_proof)),
            ));
        }
        if let Some((source, rule)) = intrinsic_codomain(element) {
            if standard_set_is_subset_eq(&source, target) {
                let source_proof = StructuralMembershipProof::new(
                    element.clone(),
                    source.clone(),
                    P::Intrinsic(rule),
                );
                return Some(if &source == target {
                    source_proof
                } else {
                    StructuralMembershipProof::new(
                        element.clone(),
                        target.clone(),
                        P::StandardSuperset(Box::new(source_proof)),
                    )
                });
            }
        }
        // No refinement search: signed/nonzero targets need known evidence,
        // exact calculation or an intrinsic signature above.
        if !matches!(target, N | Z | Q | R | C) {
            return None;
        }
        let mut child = |obj: &Obj, set: &StandardSet| {
            self.search_structural_membership(obj, set).map(Box::new)
        };
        let reason = match element {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(v)) => P::Add {
                left: child(&v.left, target)?,
                right: child(&v.right, target)?,
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(v)) if !matches!(target, N) => P::Sub {
                left: child(&v.left, target)?,
                right: child(&v.right, target)?,
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)) => P::Mul {
                left: child(&v.left, target)?,
                right: child(&v.right, target)?,
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) if matches!(target, Q | R | C) => {
                P::Div {
                    left: child(&v.left, target)?,
                    right: child(&v.right, target)?,
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(v)) if !matches!(target, N) => P::Neg {
                argument: child(&v.arg, target)?,
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(v)) => P::Abs {
                argument: child(&v.arg, if matches!(target, N) { &Z } else { target })?,
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(v)) => P::Pow {
                base: child(&v.base, target)?,
                exponent: child(&v.exponent, if matches!(target, N | Z) { &N } else { &Z })?,
            },
            // User-function/tuple carriers remain SP. A leaf can be used here
            // only if its membership was already cited above.
            _ => return None,
        };
        Some(StructuralMembershipProof::new(
            element.clone(),
            target.clone(),
            reason,
        ))
    }

    // Batch the finite carrier alternatives: compare each stored element only
    // once, not once per possible numeric set. Preserve carrier-table priority
    // and, within a carrier, the same visible-fact order as raw known lookup.
    fn lookup_structural_numeric_subset(
        &mut self,
        goal: &AtomicFact,
        element: &Obj,
        target: &StandardSet,
    ) -> Option<(
        StandardSet,
        AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
    )> {
        let sources = proper_subsets_in_membership_proof_order(target);
        if sources.is_empty() {
            return None;
        }
        let key = (goal.prop_name(), true);
        let candidates: Vec<_> = self
            .execution_environments_stack
            .iter()
            .rev()
            .filter_map(|env| {
                env.facts
                    .known_atomic_except_equality_facts
                    .by_prop
                    .get(&key)
            })
            .flat_map(|knowns| knowns.iter())
            .filter_map(|fact| match fact {
                AtomicFact::InFact(member) => Some(member.clone()),
                _ => None,
            })
            .collect();
        let mut best = None;
        let mut source_limit = sources.len();
        let mut adjacency = None;
        for known in candidates {
            let Some(element_equal) = self.lookup_known_obj_equality_with_graph(&known.element, element, &mut adjacency)
            else {
                continue;
            };
            for (index, source) in sources.iter().enumerate().take(source_limit) {
                let Some(set_equal) =
                    self.lookup_known_obj_equality_with_graph(&known.set, &Obj::StandardSet(source.clone()), &mut adjacency)
                else {
                    continue;
                };
                best = Some((
                    source.clone(),
                    AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                        cite_fact_id: known.fact_id,
                        why_parameters_of_known_fact_are_equal_to_givens: vec![
                            element_equal,
                            set_equal,
                        ],
                    },
                ));
                source_limit = index;
                break;
            }
            if source_limit == 0 {
                break;
            }
        }
        best
    }
}

fn intrinsic_codomain(element: &Obj) -> Option<(StandardSet, IntrinsicCodomain)> {
    use IntrinsicCodomain as K;
    use StandardSet::*;
    Some(match element {
        Obj::ArithmeticOperator(v) => match v {
            ArithmeticOperator::Floor(_) => (Z, K::Floor),
            ArithmeticOperator::Ceil(_) => (Z, K::Ceil),
            ArithmeticOperator::Sign(_) => (Z, K::Sign),
            ArithmeticOperator::Min(_) => (R, K::Min),
            ArithmeticOperator::Max(_) => (R, K::Max),
            ArithmeticOperator::Abs(_) => (R, K::Abs),
            _ => return None,
        },
        Obj::IntegerOperator(v) => match v {
            IntegerOperator::Mod(_) => (Z, K::Mod),
            IntegerOperator::Quot(_) => (Z, K::Quot),
            IntegerOperator::Gcd(_) => (NPos, K::Gcd),
            IntegerOperator::Lcm(_) => (N, K::Lcm),
            IntegerOperator::Factorial(_) => (NPos, K::Factorial),
        },
        Obj::ExpLogOperator(v) => match v {
            ExpLogOperator::Exp(_) => (RPos, K::Exp),
            ExpLogOperator::Sqrt(_) => (R, K::Sqrt),
            ExpLogOperator::Log(_) => (R, K::Log),
            ExpLogOperator::Ln(_) => (R, K::Ln),
        },
        Obj::TrigOperator(v) => match v {
            TrigOperator::Sin(_) => (R, K::Sin),
            TrigOperator::Cos(_) => (R, K::Cos),
            TrigOperator::Tan(_) => (R, K::Tan),
            TrigOperator::Cot(_) => (R, K::Cot),
            TrigOperator::Arcsin(_) => (R, K::Arcsin),
            TrigOperator::Arccos(_) => (R, K::Arccos),
            TrigOperator::Arctan(_) => (R, K::Arctan),
            TrigOperator::Arccot(_) => (R, K::Arccot),
        },
        Obj::ComplexOperator(v) => match v {
            ComplexOperator::RealPart(_) => (R, K::RealPart),
            ComplexOperator::ImaginaryPart(_) => (R, K::ImaginaryPart),
            ComplexOperator::ComplexAbs(_) => (R, K::ComplexAbs),
        },
        Obj::ProductShape(ProductShape::TupleDim(_)) => (N, K::TupleDim),
        Obj::ProductShape(ProductShape::CartDim(_)) => (N, K::CartDim),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) => (N, K::FiniteSetSize),
        Obj::Literal(Literal::EulerNumber(_)) => (RPos, K::EulerNumber),
        Obj::Literal(Literal::Pi(_)) => (RPos, K::Pi),
        Obj::Literal(Literal::ImaginaryUnit(_)) => (CStar, K::ImaginaryUnit),
        _ => return None,
    })
}

#[cfg(test)]
#[path = "../../../../tests/unit/execute/direct_structural_membership/tests.rs"]
mod tests;
