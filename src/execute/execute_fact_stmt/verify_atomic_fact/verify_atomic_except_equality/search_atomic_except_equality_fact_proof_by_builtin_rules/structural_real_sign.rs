//! Shared consumers of structural real-sign certificates, after ordinary WD.
use crate::prelude::*;

impl Runtime {
    pub(super) fn search_signed_numeric_membership(
        &mut self,
        fact: &InFact,
        state: VerifyState,
    ) -> Option<SignedNumericMembershipProof> {
        use StandardSet::*;
        let Obj::StandardSet(target) = &fact.set else {
            return None;
        };
        let (base, wanted) = match target {
            RPos => (R, RealSign::Positive),
            RNeg => (R, RealSign::Negative),
            RStar => (R, RealSign::Nonzero),
            QPos => (Q, RealSign::Positive),
            QNeg => (Q, RealSign::Negative),
            QStar => (Q, RealSign::Nonzero),
            // Discrete refinements keep their existing integer/natural routes,
            // including index WD evidence and its supported compiler replay.
            _ => return None,
        };
        let base = self.search_membership_of_checked_object(&fact.element, &base, state)?;
        let sign = self.search_structural_real_sign(&fact.element, state)?;
        // Packing an already known sign into a refined carrier belongs to
        // the existing RefinedNumericCarrier strategy (and its Lean replay).
        // This builtin owns composition/strengthening of sign evidence.
        if matches!(
            &sign.reason,
            StructuralRealSignReason::Known { .. }
                | StructuralRealSignReason::Membership(_)
                | StructuralRealSignReason::Closed(_)
                | StructuralRealSignReason::ZeroLiteral
        ) {
            return None;
        }
        if !sign.sign.implies(wanted) {
            return None;
        }
        Some(SignedNumericMembershipProof::new(base, sign))
    }

    pub(super) fn search_structural_real_sign_fact(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> Option<StructuralRealSignProof> {
        use RealSign as S;
        let (left, right, forward, backward) = match fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, S::Positive, S::Negative),
            AtomicFact::GreaterFact(f) => (&f.left, &f.right, S::Negative, S::Positive),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, S::Nonnegative, S::Nonpositive),
            AtomicFact::GreaterEqualFact(f) => (&f.left, &f.right, S::Nonpositive, S::Nonnegative),
            AtomicFact::NotEqualFact(f) => (&f.left, &f.right, S::Nonzero, S::Nonzero),
            _ => return None,
        };
        let is_zero =
            |obj: &Obj| matches!(obj,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0");
        let (element, wanted) = if is_zero(left) {
            (right, forward)
        } else if is_zero(right) {
            (left, backward)
        } else {
            return None;
        };
        let proof = self.search_structural_real_sign(element, state)?;
        proof.sign.implies(wanted).then_some(proof)
    }
}
