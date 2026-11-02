//! Bounded reification against one visible, checked operation contract.
use super::super::helper::{corresponding_arg_pairs, fn_obj_prefix_obj};
use super::normal_form::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub struct RingBuiltinRewriteProof {
    pub source_fact: CommRingFact,
    pub source: AtomicExceptEqualityFactKnownProof,
    pub atoms: Vec<RingAtomProof>,
    pub equalities: Vec<RingEqualityRequirement>,
    pub atom_alignments: Vec<RingEqualityDerivation>,
    pub derivation: RingEqualityDerivation,
}
pub struct RingAtomProof {
    pub object: Obj,
    pub membership_fact: InFact,
    pub membership: VerifyFactResult,
}
pub struct RingEqualityRequirement {
    pub fact: EqualFact,
    pub proof: VerifyFactResult,
}
pub enum RingEqualityDerivation {
    Known(RingEqualityRequirement),
    Polynomial(RingPolynomialEqualityProof),
    Congruence(RingCongruenceProof),
}
pub struct RingPolynomialEqualityProof {
    pub left: Obj,
    pub right: Obj,
    pub left_expression: RingExpression,
    pub right_expression: RingExpression,
    pub left_certificate: RingNormalizationCertificate,
    pub right_certificate: RingNormalizationCertificate,
}
pub struct RingCongruenceProof {
    pub left: Obj,
    pub right: Obj,
    pub children: Vec<RingEqualityDerivation>,
}

// Ephemeral, per-attempt state. No registration, cache or environment changes.
struct RingReificationContext {
    ring: CommRingFact,
    state: VerifyState,
    atoms: Vec<RingAtomProof>,
    equalities: Vec<RingEqualityRequirement>,
    atom_alignments: Vec<RingEqualityDerivation>,
    work: usize,
    ring_steps: usize,
    normalization: RingNormalizationBudget,
}
impl RingReificationContext {
    fn new(ring: CommRingFact, state: VerifyState) -> Self {
        Self {
            ring,
            state: state.without_rewrite(),
            atoms: vec![],
            equalities: vec![],
            atom_alignments: vec![],
            work: 2048,
            ring_steps: 0,
            normalization: RingNormalizationBudget::new(RingNormalizationLimits::new()),
        }
    }
    fn spend(&mut self) -> bool {
        if self.work == 0 {
            return false;
        }
        self.work -= 1;
        true
    }
}

impl Runtime {
    pub(crate) fn search_equal_fact_by_ring(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<RingBuiltinRewriteProof>> {
        let name = AtomicName::plain(crate::parse::keywords::COMM_RING.into());
        let mut candidates = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&(name.clone(), true))
            {
                for fact in facts {
                    if let AtomicFact::CommRingFact(ring) = fact {
                        if !candidates
                            .iter()
                            .any(|r: &CommRingFact| r.fact_id == ring.fact_id)
                        {
                            candidates.push(ring.clone());
                        }
                        if candidates.len() == 32 {
                            break;
                        }
                    }
                }
            }
            if candidates.len() == 32 {
                break;
            }
        }
        // A certificate is selected by a visible positive fact, never by names
        // of operations, unchecked declarations, or a new proof of its own laws.
        for ring in candidates {
            let Some(source) =
                self.lookup_known_atomic_premise(AtomicFact::CommRingFact(ring.clone()))
            else {
                continue;
            };
            let mut context = RingReificationContext::new(ring.clone(), state);
            if let Some(derivation) =
                self.ring_equality(&fact.left, &fact.right, &mut context, 0)?
            {
                if context.ring_steps == 0 {
                    continue;
                }
                return Ok(Some(RingBuiltinRewriteProof {
                    source_fact: ring,
                    source,
                    atoms: context.atoms,
                    equalities: context.equalities,
                    atom_alignments: context.atom_alignments,
                    derivation,
                }));
            }
        }
        Ok(None)
    }

    fn ring_known_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        context: &mut RingReificationContext,
    ) -> RuntimeResult<Option<RingEqualityRequirement>> {
        if !context.spend() {
            return Ok(None);
        }
        if left.ir() != right.ir() && self.equivalence_class_path(left, right).is_none() {
            return Ok(None);
        }
        let fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        };
        // Only existing equality evidence / structural equality here; no new
        // forall instantiation, unfolding, or rewrite permission is introduced.
        let proof =
            self.verify_equal_fact(&fact, context.state.capped_at(VerifyStateLevel::Strategy))?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(RingEqualityRequirement { fact, proof }))
    }

    fn ring_objects_align(
        &mut self,
        left: &Obj,
        right: &Obj,
        context: &mut RingReificationContext,
    ) -> RuntimeResult<bool> {
        if left.ir() == right.ir() {
            return Ok(true);
        }
        let Some(proof) = self.ring_known_equality(left, right, context)? else {
            return Ok(false);
        };
        context.equalities.push(proof);
        Ok(true)
    }

    fn ring_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        context: &mut RingReificationContext,
        depth: usize,
    ) -> RuntimeResult<Option<RingEqualityDerivation>> {
        if depth > 64 || !context.spend() {
            return Ok(None);
        }
        if let Some(proof) = self.ring_known_equality(left, right, context)? {
            return Ok(Some(RingEqualityDerivation::Known(proof)));
        }
        if let Some(left_expression) = self.ring_reify(left, context, depth + 1)? {
            if let Some(right_expression) = self.ring_reify(right, context, depth + 1)? {
                if let Some(left_certificate) =
                    normalize_ring_expression(&left_expression, &mut context.normalization)
                {
                    if let Some(right_certificate) =
                        normalize_ring_expression(&right_expression, &mut context.normalization)
                    {
                        if left_certificate.nodes[left_certificate.root].polynomial
                            == right_certificate.nodes[right_certificate.root].polynomial
                        {
                            context.ring_steps += 1;
                            return Ok(Some(RingEqualityDerivation::Polynomial(
                                RingPolynomialEqualityProof {
                                    left: left.clone(),
                                    right: right.clone(),
                                    left_expression,
                                    right_expression,
                                    left_certificate,
                                    right_certificate,
                                },
                            )));
                        }
                    }
                }
            }
        }
        self.ring_congruence(left, right, context, depth + 1)
    }

    fn ring_congruence(
        &mut self,
        left: &Obj,
        right: &Obj,
        context: &mut RingReificationContext,
        depth: usize,
    ) -> RuntimeResult<Option<RingEqualityDerivation>> {
        if depth > 64 || !context.spend() {
            return Ok(None);
        }
        let Some(pairs) = corresponding_arg_pairs(left, right) else {
            return Ok(None);
        };
        if pairs.is_empty() {
            return Ok(None);
        }
        let mut children = Vec::new();
        // The shape helper returns strictly smaller original subterms. This
        // composes congruence without another top-level verifier/rewrite call.
        for (a, b) in pairs {
            let Some(proof) = self.ring_equality(&a, &b, context, depth + 1)? else {
                return Ok(None);
            };
            children.push(proof);
        }
        Ok(Some(RingEqualityDerivation::Congruence(
            RingCongruenceProof {
                left: left.clone(),
                right: right.clone(),
                children,
            },
        )))
    }

    fn ring_reify(
        &mut self,
        obj: &Obj,
        context: &mut RingReificationContext,
        depth: usize,
    ) -> RuntimeResult<Option<RingExpression>> {
        if depth > 64 || !context.spend() {
            return Ok(None);
        }
        if self.ring_objects_align(obj, &context.ring.zero.clone(), context)? {
            return Ok(Some(RingExpression::Zero));
        }
        if self.ring_objects_align(obj, &context.ring.one.clone(), context)? {
            return Ok(Some(RingExpression::One));
        }
        if let Obj::FnObj(call) = obj {
            if let Some(args) = call.body.last() {
                let head = fn_obj_prefix_obj(call, call.body.len() - 1);
                for (operation, arity, tag) in [
                    (context.ring.add.clone(), 2, 0),
                    (context.ring.mul.clone(), 2, 1),
                    (context.ring.neg.clone(), 1, 2),
                ] {
                    if args.len() != arity
                        || !self.ring_objects_align(&head, &operation, context)?
                    {
                        continue;
                    }
                    let Some(a) = self.ring_reify(&args[0], context, depth + 1)? else {
                        return Ok(None);
                    };
                    if tag == 2 {
                        return Ok(Some(RingExpression::Neg(Box::new(a))));
                    }
                    let Some(b) = self.ring_reify(&args[1], context, depth + 1)? else {
                        return Ok(None);
                    };
                    return Ok(Some(if tag == 0 {
                        RingExpression::Add(Box::new(a), Box::new(b))
                    } else {
                        RingExpression::Mul(Box::new(a), Box::new(b))
                    }));
                }
            }
        }
        // Native scalar literals, divisions, foreign operations and opaque
        // calls are atoms, never integer coefficients of the selected ring.
        for i in 0..context.atoms.len() {
            let known = context.atoms[i].object.clone();
            if self.ring_objects_align(obj, &known, context)? {
                return Ok(Some(RingExpression::Atom(i)));
            }
            if let Some(proof) = self.ring_congruence(obj, &known, context, depth + 1)? {
                // This derivation aligns an opaque atom with the already typed
                // representative; retain it as part of the parent derivation.
                context.atom_alignments.push(proof);
                return Ok(Some(RingExpression::Atom(i)));
            }
        }
        if context.atoms.len() >= 64 {
            return Ok(None);
        }
        let membership_fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: context.ring.carrier.clone(),
            line_file: None,
        };
        let membership = self.verify_fact(
            &membership_fact.clone().into(),
            context.state.capped_at(VerifyStateLevel::BuiltinRule),
        )?;
        if membership.is_failed() {
            return Ok(None);
        }
        let index = context.atoms.len();
        context.atoms.push(RingAtomProof {
            object: obj.clone(),
            membership_fact,
            membership,
        });
        Ok(Some(RingExpression::Atom(index)))
    }
}
