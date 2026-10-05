//! Floor and ceiling are weakly monotone on the reals.
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, LessEqualFact};
use crate::ast::obj::{ArithmeticOperator, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FloorMonotoneProof { pub argument_order: VerifyFactResult }
pub struct CeilMonotoneProof { pub argument_order: VerifyFactResult }

impl Runtime {
    pub(super) fn search_rounding_order(&mut self,fact:&LessEqualFact,state:VerifyState)
        -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // x<=y implies floor(x)<=floor(y) and ceil(x)<=ceil(y); WD checks real arguments.
        let (x,y,floor)=match (&fact.left,&fact.right) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Floor(x)),Obj::ArithmeticOperator(ArithmeticOperator::Floor(y))) => (&*x.arg,&*y.arg,true),
            (Obj::ArithmeticOperator(ArithmeticOperator::Ceil(x)),Obj::ArithmeticOperator(ArithmeticOperator::Ceil(y))) => (&*x.arg,&*y.arg,false),
            _ => return Ok(None),
        };
        let goal:Fact=LessEqualFact{fact_id:self.global_ids.allocate_fact_id(),left:x.clone(),right:y.clone(),line_file:fact.line_file.clone()}.into();
        let argument_order=self.verify_builtin_rule_premise(&goal,state)?;
        if argument_order.is_failed(){return Ok(None);}
        Ok(Some(if floor {
            LessEqualFactSearchProofByBuiltinRule::FloorMonotone(FloorMonotoneProof{argument_order})
        } else {
            LessEqualFactSearchProofByBuiltinRule::CeilMonotone(CeilMonotoneProof{argument_order})
        }))
    }
}
