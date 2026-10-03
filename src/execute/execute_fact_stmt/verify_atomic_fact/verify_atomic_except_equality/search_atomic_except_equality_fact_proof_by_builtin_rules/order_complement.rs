use crate::ast::fact::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::runtime::{Runtime, RuntimeResult};
use crate::ast::obj::{Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};

pub struct FromKnownOrderComplementBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
    pub real_carrier_proofs: Vec<VerifyFactResult>,
}

impl Runtime {
    // Real order is total: e.g. not (a <= b) iff a > b. The rule proves
    // both real carriers explicitly; object WD alone does not ensure them. Only an actual known complement
    // counts as evidence; failure to prove a comparison is never its negation.
    pub(super) fn known_order_complement(
        &mut self,
        goal: AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FromKnownOrderComplementBuiltinRuleProof>> {
        let fact_id = self.global_ids.allocate_fact_id();
        let premise: AtomicFact = match goal {
            AtomicFact::LessFact(f) => NotGreaterEqualFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::GreaterFact(f) => NotLessEqualFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::LessEqualFact(f) => NotGreaterFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::GreaterEqualFact(f) => NotLessFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::NotLessFact(f) => GreaterEqualFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::NotGreaterFact(f) => LessEqualFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::NotLessEqualFact(f) => GreaterFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            AtomicFact::NotGreaterEqualFact(f) => LessFact { fact_id, left: f.left, right: f.right, line_file: f.line_file }.into(),
            _ => return Ok(None),
        };
        let Some(premise_proof) = self.lookup_known_atomic_premise(premise.clone()) else {
            return Ok(None);
        };
        let mut real_carrier_proofs = Vec::new();
        for element in atomic_fact_args_ref(&premise) {
            let membership: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: element.clone(), set: Obj::StandardSet(StandardSet::R), line_file: None,
            }.into();
            let proof = self.verify_builtin_rule_premise(&membership, verify_state)?;
            if proof.is_failed() { return Ok(None); }
            real_carrier_proofs.push(proof);
        }
        Ok(Some(FromKnownOrderComplementBuiltinRuleProof { premise_proof, real_carrier_proofs }))
    }
}
