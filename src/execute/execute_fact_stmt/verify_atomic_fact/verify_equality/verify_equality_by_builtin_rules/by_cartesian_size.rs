//! Cardinality of a finite Cartesian product, for any supported arity.
use crate::ast::fact::{EqualFact, Fact, IsFiniteSetFact};
use crate::ast::obj::{FiniteSetSize, FiniteSetStat, Literal, Number, Obj, ProductShape};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::helper::mul_objs;
use crate::runtime::{Runtime, RuntimeResult};

pub struct CartesianSizeProof {
    pub factor_finiteness: Vec<VerifyFactResult>,
}

impl Runtime {
    pub(super) fn search_cartesian_size(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<CartesianSizeProof>> {
        // |cart(A,B,...)| = |A|*|B|*...; finiteness is required for each size.
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = left else {
                continue;
            };
            let Obj::ProductShape(ProductShape::Cart(cart)) = &*size.set else {
                continue;
            };
            let mut product = Obj::Literal(Literal::Number(Number::new("1".into())));
            for factor in &cart.args {
                let size = Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                    set: factor.clone(),
                }));
                product = mul_objs(product, size);
            }
            if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                &product, right,
            ) {
                continue;
            }
            let mut factor_finiteness = Vec::new();
            for factor in &cart.args {
                let goal: Fact = IsFiniteSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: *factor.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let proof = self.verify_builtin_rule_premise(&goal, state.clone())?;
                if proof.is_failed() {
                    break;
                }
                factor_finiteness.push(proof);
            }
            if factor_finiteness.len() == cart.args.len() {
                return Ok(Some(CartesianSizeProof { factor_finiteness }));
            }
        }
        Ok(None)
    }
}
