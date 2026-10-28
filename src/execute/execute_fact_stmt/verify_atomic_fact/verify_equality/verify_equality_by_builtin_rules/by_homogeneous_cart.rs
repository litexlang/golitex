use crate::prelude::*;

pub struct HomogeneousCartesianEqualsFiniteSequenceBuiltinRuleProof {
    pub dimension: usize,
    pub length_equal: Box<EqualFactSearchedProof>,
    pub factor_equalities: Vec<EqualFactSearchedProof>,
}

impl Runtime {
    // Only these two constructors, with direct/closed equality leaves. This is
    // also the bounded equality consumer used by subset and Euclidean interior.
    pub(crate) fn search_homogeneous_cartesian_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<HomogeneousCartesianEqualsFiniteSequenceBuiltinRuleProof> {
        for (cart, sequence) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let (
                Obj::ProductShape(ProductShape::Cart(cart)),
                Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)),
            ) = (cart, sequence)
            else {
                continue;
            };
            let dimension = cart.args.len();
            let length = Obj::Literal(Literal::Number(Number {
                normalized_value: dimension.to_string(),
            }));
            let length_fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *sequence.n.clone(),
                right: length,
                line_file: None,
            };
            let Some(length_equal) = self.search_equal_fact_proof_directly(&length_fact) else {
                continue;
            };
            let mut factor_equalities = Vec::new();
            for factor in &cart.args {
                let equal = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: *factor.clone(),
                    right: *sequence.set.clone(),
                    line_file: None,
                };
                let Some(proof) = self.search_equal_fact_proof_directly(&equal) else {
                    break;
                };
                factor_equalities.push(proof);
            }
            if factor_equalities.len() == dimension {
                return Some(HomogeneousCartesianEqualsFiniteSequenceBuiltinRuleProof {
                    dimension,
                    length_equal: Box::new(length_equal),
                    factor_equalities,
                });
            }
        }
        None
    }
}
