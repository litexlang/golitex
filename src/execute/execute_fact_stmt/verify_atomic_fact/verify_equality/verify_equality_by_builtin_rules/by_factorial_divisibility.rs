//! An earlier factorial divides a later factorial.
use crate::ast::fact::{EqualFact, Fact, InFact, LessEqualFact};
use crate::ast::obj::{IntegerOperator, Literal, Number, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FactorialDivisibilityProof {
    pub earlier_natural: VerifyFactResult,
    pub later_natural: VerifyFactResult,
    pub order: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_factorial_divisibility(&mut self, fact:&EqualFact,state:VerifyState)
        -> RuntimeResult<Option<FactorialDivisibilityProof>> {
        // m,n in N and m<=n imply n! % m! = 0; whole-fact WD precedes this rule.
        for (remainder,zero) in [(&fact.left,&fact.right),(&fact.right,&fact.left)] {
            if zero.ir()!=Obj::Literal(Literal::Number(Number::new("0".into()))).ir() { continue; }
            let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = remainder else {continue;};
            let (Obj::IntegerOperator(IntegerOperator::Factorial(n)),Obj::IntegerOperator(IntegerOperator::Factorial(m)))=(&*rem.left,&*rem.right) else {continue;};
            let mf:Fact=InFact {fact_id:self.global_ids.allocate_fact_id(),element:*m.arg.clone(),set:Obj::StandardSet(StandardSet::N),line_file:fact.line_file.clone()}.into();
            let earlier_natural=self.verify_builtin_rule_premise(&mf,state)?;
            if earlier_natural.is_failed(){continue;}
            let nf:Fact=InFact {fact_id:self.global_ids.allocate_fact_id(),element:*n.arg.clone(),set:Obj::StandardSet(StandardSet::N),line_file:fact.line_file.clone()}.into();
            let later_natural=self.verify_builtin_rule_premise(&nf,state)?;
            if later_natural.is_failed(){continue;}
            let bound:Fact=LessEqualFact {fact_id:self.global_ids.allocate_fact_id(),left:*m.arg.clone(),right:*n.arg.clone(),line_file:fact.line_file.clone()}.into();
            let order=self.verify_builtin_rule_premise(&bound,state)?;
            if !order.is_failed(){return Ok(Some(FactorialDivisibilityProof{earlier_natural,later_natural,order}));}
        }
        Ok(None)
    }
}
