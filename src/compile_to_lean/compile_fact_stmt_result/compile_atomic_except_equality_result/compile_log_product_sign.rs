use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;
impl LitexToLeanCompiler {
    fn compile_sign_constant(
        &self,
        object: &Obj,
        value: i128,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if EvalRational::from_obj(object) != EvalRational::new(value, 1) {
            return Err(invalid("ConstantEndpoint"));
        }
        let term = self.compile_object_reference(object, position)?;
        let observed = self.compile_numeric_observation(object, position)?;
        let proof=format!("(show Litex.denote {term} = M.number ({value} : ℂ) from (({}).trans (congrArg M.number (by norm_num))))",observed.1);
        Ok((term, proof))
    }
    pub(super) fn compile_natural_log_sign(
        &self,
        goal: &AtomicFact,
        positive: bool,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (object, zero) = if positive { (high, low) } else { (low, high) };
        let Obj::ExpLogOperator(ExpLogOperator::Ln(ln)) = object else {
            return Err(invalid("LogSubject"));
        };
        let (a, b, known_strict) = source_order_oriented(&premise.fact)?;
        let (one, arg) = if positive { (a, b) } else { (b, a) };
        if !strict || !known_strict || arg.ir() != ln.arg.ir() {
            return Err(invalid("LogRequirement"));
        }
        let (one_term, one_eq) = self.compile_sign_constant(one, 1, position)?;
        let known = self.compile_order_known_premise(premise, position)?.1;
        let arg = self.compile_object_reference(&ln.arg, position)?;
        let known = if positive {
            format!("(Litex.ltOfSame {one_term} (Litex.number 1) {arg} {arg} {one_eq} rfl {known})")
        } else {
            format!("(Litex.ltOfSame {arg} {arg} {one_term} (Litex.number 1) rfl {one_eq} {known})")
        };
        let term = self.compile_object_reference(object, position)?;
        let law = if positive {
            "naturalLogPositiveAboveOneValue"
        } else {
            "naturalLogNegativeBelowOneValue"
        };
        let proof = format!("(Litex.{law} {term} {known})");
        let (zero_term, zero_eq) = self.compile_sign_constant(zero, 0, position)?;
        Ok(if positive {
            format!("(Litex.ltOfSame (Litex.number 0) {zero_term} {term} {term} {zero_eq}.symm rfl {proof})")
        } else {
            format!("(Litex.ltOfSame {term} {term} (Litex.number 0) {zero_term} rfl {zero_eq}.symm {proof})")
        })
    }
    pub(super) fn compile_mixed_product_sign(
        &self,
        goal: &AtomicFact,
        strict: bool,
        positive: &VerifyFactResult,
        negative: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (product, zero, goal_strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = product else {
            return Err(invalid("ProductSubject"));
        };
        let (Fact::AtomicFact(hp), Fact::AtomicFact(hn)) =
            (source_subject(positive)?, source_subject(negative)?)
        else {
            return Err(invalid("ProductChildren"));
        };
        let (pzero, pfactor, pstrict) = source_order_oriented(&hp)?;
        let (nfactor, nzero, nstrict) = source_order_oriented(&hn)?;
        if goal_strict != strict || pstrict != strict || !nstrict {
            return Err(invalid("ProductStrictness"));
        }
        let reverse = if pfactor.ir() == p.left.ir() && nfactor.ir() == p.right.ir() {
            false
        } else if pfactor.ir() == p.right.ir() && nfactor.ir() == p.left.ir() {
            true
        } else {
            return Err(invalid("ProductFactors"));
        };
        let hp = self
            .compile_verify(positive, &position.atomic_search_prior(0)?)?
            .1;
        let hn = self
            .compile_verify(negative, &position.atomic_search_prior(1)?)?
            .1;
        let complete = position.atomic_search_prior(2)?;
        let (pzero_term, pzero_eq) = self.compile_sign_constant(pzero, 0, &complete)?;
        let (nzero_term, nzero_eq) = self.compile_sign_constant(nzero, 0, &complete)?;
        let pfactor = self.compile_object_reference(pfactor, &complete)?;
        let nfactor = self.compile_object_reference(nfactor, &complete)?;
        let transport = if strict { "ltOfSame" } else { "leOfSame" };
        let hp=format!("(Litex.{transport} {pzero_term} (Litex.number 0) {pfactor} {pfactor} {pzero_eq} rfl {hp})");
        let hn=format!("(Litex.ltOfSame {nfactor} {nfactor} {nzero_term} (Litex.number 0) rfl {nzero_eq} {hn})");
        let product = self.compile_object_reference(product, &complete)?;
        let law = if strict {
            "positiveNegativeProductValue"
        } else {
            "nonnegativeNegativeProductValue"
        };
        let proof = format!("(Litex.{law} {product} {reverse} {hp} {hn})");
        let (zero_term, zero_eq) = self.compile_sign_constant(zero, 0, &complete)?;
        Ok(format!("(Litex.{transport} {product} {product} (Litex.number 0) {zero_term} rfl {zero_eq}.symm {proof})"))
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("LogProductSign/{part}"))
}
