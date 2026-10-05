//! Reconstruct a Cartesian product from its checked dimension and every factor.
use crate::ast::fact::{EqualFact, Fact, IsCartFact};
use crate::ast::obj::{CartDim, Literal, Number, Obj, ProductShape, Proj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct CartReconstructionProof {
    pub cartesian: VerifyFactResult,
    pub dimension: VerifyFactResult,
    pub factors: Vec<VerifyFactResult>,
}

impl Runtime {
    pub(super) fn search_cart_reconstruction(&mut self,fact:&EqualFact,state:VerifyState)
        -> RuntimeResult<Option<CartReconstructionProof>> {
        // is_cart(K), dim(K)=n and proj(K,j)=Aj for every j=1..n imply K=cart(A1,...,An).
        for (known,literal) in [(&fact.left,&fact.right),(&fact.right,&fact.left)] {
            let Obj::ProductShape(ProductShape::Cart(cart))=literal else {continue;};
            if cart.args.is_empty(){continue;}
            let cf:Fact=IsCartFact{fact_id:self.global_ids.allocate_fact_id(),set:known.clone(),line_file:fact.line_file.clone()}.into();
            let cartesian=self.verify_builtin_rule_premise(&cf,state)?;
            if cartesian.is_failed(){continue;}
            let dim=Obj::ProductShape(ProductShape::CartDim(CartDim{set:Box::new(known.clone())}));
            let df:Fact=EqualFact{fact_id:self.global_ids.allocate_fact_id(),left:dim,right:Obj::Literal(Literal::Number(Number::new(cart.args.len().to_string()))),line_file:fact.line_file.clone()}.into();
            let dimension=self.verify_builtin_rule_premise(&df,state)?;
            if dimension.is_failed(){continue;}
            let mut factors=Vec::new();
            for (index,factor) in cart.args.iter().enumerate() {
                let projection=Obj::ProductShape(ProductShape::Proj(Proj{set:Box::new(known.clone()),dim:Box::new(Obj::Literal(Literal::Number(Number::new((index+1).to_string()))))}));
                let pf:Fact=EqualFact{fact_id:self.global_ids.allocate_fact_id(),left:projection,right:*factor.clone(),line_file:fact.line_file.clone()}.into();
                let proof=self.verify_builtin_rule_premise(&pf,state)?;
                if proof.is_failed(){break;}
                factors.push(proof);
            }
            if factors.len()==cart.args.len(){return Ok(Some(CartReconstructionProof{cartesian,dimension,factors}));}
        }
        Ok(None)
    }
}
