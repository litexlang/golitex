//! Fixed trigonometric nonzero transport and scalar zero-alias consumption.
use super::not_equal::NotEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{AtomicFact, NotEqualFact};
use crate::ast::obj::{ArithmeticOperator as A, Cos, Literal, Number, Obj, Sin, TrigOperator as T};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::rational_expression::exact_rational::EvalRational;
use crate::runtime::{Runtime, RuntimeResult};

pub struct SinNonzeroNegationProof {
    pub source_nonzero: AtomicExceptEqualityFactKnownProof,
}
impl SinNonzeroNegationProof {
    pub fn new(source_nonzero: AtomicExceptEqualityFactKnownProof) -> Self { Self { source_nonzero } }
}
pub struct CosNonzeroNegationProof {
    pub source_nonzero: AtomicExceptEqualityFactKnownProof,
}
impl CosNonzeroNegationProof {
    pub fn new(source_nonzero: AtomicExceptEqualityFactKnownProof) -> Self { Self { source_nonzero } }
}
pub struct SinNonzeroIntegerPiShiftProof {
    pub source_nonzero: AtomicExceptEqualityFactKnownProof,
    pub coefficient: Obj,
}
impl SinNonzeroIntegerPiShiftProof {
    pub fn new(source_nonzero: AtomicExceptEqualityFactKnownProof, coefficient: Obj) -> Self { Self { source_nonzero, coefficient } }
}
pub struct CosNonzeroIntegerPiShiftProof {
    pub source_nonzero: AtomicExceptEqualityFactKnownProof,
    pub coefficient: Obj,
}
impl CosNonzeroIntegerPiShiftProof {
    pub fn new(source_nonzero: AtomicExceptEqualityFactKnownProof, coefficient: Obj) -> Self { Self { source_nonzero, coefficient } }
}
pub struct TanNonzeroFromSinProof {
    pub numerator_nonzero: AtomicExceptEqualityFactKnownProof,
}
impl TanNonzeroFromSinProof {
    pub fn new(numerator_nonzero: AtomicExceptEqualityFactKnownProof) -> Self { Self { numerator_nonzero } }
}
pub struct CotNonzeroFromCosProof {
    pub numerator_nonzero: AtomicExceptEqualityFactKnownProof,
}
impl CotNonzeroFromCosProof {
    pub fn new(numerator_nonzero: AtomicExceptEqualityFactKnownProof) -> Self { Self { numerator_nonzero } }
}
pub struct EulerNonunitProof;
pub struct ProductFactorNonzeroWithZeroAliasProof {
    pub product_nonzero: AtomicExceptEqualityFactKnownProof,
    pub zero_equality: Box<EqualFactSearchedProof>,
}
impl ProductFactorNonzeroWithZeroAliasProof {
    pub fn new(product_nonzero: AtomicExceptEqualityFactKnownProof, zero_equality: Box<EqualFactSearchedProof>) -> Self { Self { product_nonzero, zero_equality } }
}

impl Runtime {
    pub(super) fn search_scalar_nonzero_relation(
        &mut self, fact: &NotEqualFact,
    ) -> RuntimeResult<Option<NotEqualFactSearchProofByBuiltinRule>> {
        use NotEqualFactSearchProofByBuiltinRule as P;
        // e>1, hence e!=1; no arithmetic approximation is involved.
        for (constant, one) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if matches!(constant, Obj::Literal(Literal::EulerNumber(_)))
                && EvalRational::from_obj(one) == EvalRational::new(1, 1) {
                return Ok(Some(P::EulerNonunit(EulerNonunitProof)));
            }
        }
        for (value, zero) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if !EvalRational::from_obj(zero).is_some_and(|n| n.is_zero()) { continue; }
            // sin(-x)=-sin(x), cos(-x)=cos(x); integer pi shifts preserve
            // nonzero sine/cosine. Read only the prescribed source endpoint.
            for sine in [true, false] {
                let argument = match (value, sine) {
                    (Obj::TrigOperator(T::Sin(s)), true) => &*s.arg,
                    (Obj::TrigOperator(T::Cos(c)), false) => &*c.arg,
                    _ => continue,
                };
                let negated = match argument {
                    Obj::ArithmeticOperator(A::Neg(neg)) => Some(&*neg.arg),
                    Obj::ArithmeticOperator(A::Sub(sub)) if EvalRational::from_obj(&sub.left).is_some_and(|v| v.is_zero()) => Some(&*sub.right),
                    _ => None,
                };
                if let Some(base) = negated {
                    let source = trig(base, sine);
                    if let Some(source_nonzero) = self.known_not_equal_proof(&source, zero)
                        .or_else(|| self.known_not_equal_proof(zero, &source)) {
                        return Ok(Some(if sine { P::SinNonzeroNegation(SinNonzeroNegationProof::new(source_nonzero)) }
                            else { P::CosNonzeroNegation(CosNonzeroNegationProof::new(source_nonzero)) }));
                    }
                }
                let shifts = match argument {
                    Obj::ArithmeticOperator(A::Add(sum)) => vec![(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)],
                    Obj::ArithmeticOperator(A::Sub(sub)) => vec![(&*sub.left, &*sub.right)],
                    _ => Vec::new(),
                };
                for (base, shift) in shifts {
                    let Some(coefficient) = crate::rational_expression::pi_multiple::pi_coefficient(shift) else { continue; };
                    if !EvalRational::from_obj(&coefficient).is_some_and(|v| v.to_i128_if_integer().is_some()) { continue; }
                    let source = trig(base, sine);
                    if let Some(source_nonzero) = self.known_not_equal_proof(&source, zero)
                        .or_else(|| self.known_not_equal_proof(zero, &source)) {
                        return Ok(Some(if sine { P::SinNonzeroIntegerPiShift(SinNonzeroIntegerPiShiftProof::new(source_nonzero, coefficient)) }
                            else { P::CosNonzeroIntegerPiShift(CosNonzeroIntegerPiShiftProof::new(source_nonzero, coefficient)) }));
                    }
                }
            }
            // A defined tan/cot quotient is nonzero exactly when its numerator
            // is nonzero. Parent WD retains the other trigonometric denominator.
            let numerator = match value {
                Obj::TrigOperator(T::Tan(t)) => Some((trig(&t.arg, true), true)),
                Obj::TrigOperator(T::Cot(c)) => Some((trig(&c.arg, false), false)),
                _ => None,
            };
            if let Some((numerator, tangent)) = numerator {
                if let Some(numerator_nonzero) = self.known_not_equal_proof(&numerator, zero)
                    .or_else(|| self.known_not_equal_proof(zero, &numerator)) {
                    return Ok(Some(if tangent { P::TanNonzeroFromSin(TanNonzeroFromSinProof::new(numerator_nonzero)) }
                        else { P::CotNonzeroFromCos(CotNonzeroFromCosProof::new(numerator_nonzero)) }));
                }
            }
            // a*b!=z and a checked z=0 imply each factor is nonzero.
            // Inspect only stored nonzero products containing this exact factor;
            // no zero-equivalence-class or arbitrary graph endpoint discovery.
            let mut candidates = Vec::new();
            for env in self.execution_environments_stack.iter().rev() {
                for knowns in env.facts.known_atomic_except_equality_facts.by_prop.values() {
                    for known in knowns {
                        let AtomicFact::NotEqualFact(source) = known else { continue; };
                        for (product, alias) in [(&source.left, &source.right), (&source.right, &source.left)] {
                            let Obj::ArithmeticOperator(A::Mul(m)) = product else { continue; };
                            if m.left.ir() == value.ir() || m.right.ir() == value.ir() {
                                candidates.push((known.clone(), alias.clone()));
                            }
                        }
                    }
                }
            }
            for (source, alias) in candidates {
                if EvalRational::from_obj(&alias).is_some_and(|n| n.is_zero()) { continue; }
                let canonical_zero = Obj::Literal(Literal::Number(Number::new("0".into())));
                let Some(zero_equality) = self.lookup_exact_property_obj_equality(&alias, &canonical_zero) else { continue; };
                let Some(product_nonzero) = self.lookup_known_atomic_premise(source) else { continue; };
                return Ok(Some(P::ProductFactorNonzeroWithZeroAlias(ProductFactorNonzeroWithZeroAliasProof::new(
                    product_nonzero, Box::new(zero_equality),
                ))));
            }
        }
        Ok(None)
    }
}
fn trig(argument: &Obj, sine: bool) -> Obj {
    if sine { Obj::TrigOperator(T::Sin(Sin { arg: Box::new(argument.clone()) })) }
    else { Obj::TrigOperator(T::Cos(Cos { arg: Box::new(argument.clone()) })) }
}
