//! Convert a checked scalar division equation and its product equation.
use crate::ast::fact::{EqualFact, Fact};
use crate::ast::obj::{ArithmeticOperator, Div, Mul, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub enum ScalarDivisionRelationProof {
    ProductFromDivision(ProductFromDivisionProof),
    DivisionFromProduct(DivisionFromProductProof),
}
pub struct ProductFromDivisionProof {
    pub division_equation: VerifyFactResult,
}
impl ProductFromDivisionProof {
    pub fn new(division_equation: VerifyFactResult) -> Self { Self { division_equation } }
}
pub struct DivisionFromProductProof {
    pub product_equation: VerifyFactResult,
}
impl DivisionFromProductProof {
    pub fn new(product_equation: VerifyFactResult) -> Self { Self { product_equation } }
}
impl ScalarDivisionRelationProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ProductFromDivision(_) => "ProductFromDivision",
            Self::DivisionFromProduct(_) => "DivisionFromProduct",
        }
    }
}
impl Runtime {
    pub(super) fn search_scalar_division_relation(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<ScalarDivisionRelationProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            // a/b=c => a=c*b. Verify the actual source equation, including
            // division WD, at the inherited premise ceiling. Its cached WD
            // handles a denominator such as b*d without rediscovering a proof.
            if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = right {
                for (factor, denominator) in [(&*product.left, &*product.right), (&*product.right, &*product.left)] {
                    let quotient = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                        left: Box::new(left.clone()), right: Box::new(denominator.clone()),
                    }));
                    let source: Fact = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(), left: quotient,
                        right: factor.clone(), line_file: fact.line_file.clone(),
                    }.into();
                    let division_equation = self.verify_builtin_rule_premise(&source, state)?;
                    if !division_equation.is_failed() {
                        return Ok(Some(ScalarDivisionRelationProof::ProductFromDivision(
                            ProductFromDivisionProof::new(division_equation),
                        )));
                    }
                }
            }
            // a=c*b => a/b=c. The parent division goal WD already owns b!=0.
            if let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = left {
                for (a, b) in [(right, &*quotient.right), (&*quotient.right, right)] {
                    let product = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                        left: Box::new(a.clone()), right: Box::new(b.clone()),
                    }));
                    let source: Fact = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(), left: *quotient.left.clone(),
                        right: product, line_file: fact.line_file.clone(),
                    }.into();
                    let product_equation = self.verify_builtin_rule_premise(&source, state)?;
                    if !product_equation.is_failed() {
                        return Ok(Some(ScalarDivisionRelationProof::DivisionFromProduct(
                            DivisionFromProductProof::new(product_equation),
                        )));
                    }
                }
            }
        }
        Ok(None)
    }
}
