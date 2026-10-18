//! Read-only conversion of an already stored zero remainder into divisibility.
//! No truth search, witness search or publication occurs here.
use super::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub struct KnownZeroRemainderProof {
    pub dividend: Obj,
    pub divisor: Obj,
    pub zero_remainder: Box<EqualFactSearchedProof>,
}

impl Runtime {
    pub(in crate::execute) fn lookup_known_zero_remainder(
        &mut self,
        dividend: &Obj,
        divisor: &Obj,
    ) -> Option<KnownZeroRemainderProof> {
        let remainder = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(dividend.clone()),
            right: Box::new(divisor.clone()),
        }));
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        let zero_remainder = self.lookup_known_obj_equality(&remainder, &zero)?;
        Some(KnownZeroRemainderProof {
            dividend: dividend.clone(),
            divisor: divisor.clone(),
            zero_remainder: Box::new(zero_remainder),
        })
    }

    pub(in crate::execute) fn lookup_known_dvd_premise(
        &mut self,
        dividend: &Obj,
        divisor: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let fact: AtomicFact = DvdFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: dividend.clone(),
            right: divisor.clone(),
            line_file: None,
        }
        .into();
        let searched_proof = if let Some(p) = self.lookup_known_atomic_fact(&fact) {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p)
        } else {
            AtomicExceptEqualityFactSearchedProof::ByKnownZeroRemainder(
                self.lookup_known_zero_remainder(dividend, divisor)?,
            )
        };
        Some(AtomicExceptEqualityFactKnownProof {
            fact,
            searched_proof: Box::new(searched_proof),
        })
    }
}
