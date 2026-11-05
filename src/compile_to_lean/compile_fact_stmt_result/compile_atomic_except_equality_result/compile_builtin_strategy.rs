use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_integer_range_membership_strategy(
        &self,
        goal: &AtomicFact,
        closed: bool,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let wrong = || LeanCompileError::unsupported("IntegerRangeMembership/SourceStages");
        let AtomicFact::InFact(member) = goal else {
            return Err(wrong());
        };
        let (start, finish) = match (&member.set, closed) {
            (Obj::SetFormer(SetFormer::ClosedRange(r)), true) => (&r.start, &r.end),
            (Obj::SetFormer(SetFormer::Range(r)), false) => (&r.start, &r.end),
            _ => return Err(wrong()),
        };
        if requirements.len() != 3
            || proofs.len() != 3
            || !matches!(&requirements[0], Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element == member.element && f.set == Obj::StandardSet(StandardSet::Z))
            || !matches!(&requirements[1], Fact::AtomicFact(AtomicFact::LessEqualFact(f))
                if &f.left == start.as_ref() && f.right == member.element)
            || !(match &requirements[2] {
                Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if closed => {
                    f.left == member.element && &f.right == finish.as_ref()
                }
                Fact::AtomicFact(AtomicFact::LessFact(f)) if !closed => {
                    f.left == member.element && &f.right == finish.as_ref()
                }
                _ => false,
            })
        {
            return Err(wrong());
        }
        let mut definitions = Vec::new();
        for (index, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *requirement {
                return Err(wrong());
            }
            let prior = position.atomic_search_prior(index)?;
            let compiled = self.compile_verify(proof, &prior)?;
            // This method returns a proof expression even at a global WD
            // site. Requirement producers are lexical haves inside that term.
            definitions.push(self.emit_fact(requirement, compiled, 0, true, &prior)?);
        }
        let complete = position.atomic_search_prior(3)?;
        let range = self.compile_object_reference(&member.set, &complete)?;
        let point = self.compile_object_reference(&member.element, &complete)?;
        let integer = format!("h_{}", requirements[0].fact_id().value());
        let lower = format!("h_{}", requirements[1].fact_id().value());
        let upper = format!("h_{}", requirements[2].fact_id().value());
        let family = if closed { "ClosedRange" } else { "Range" };
        let relation = if closed { "≤" } else { "<" };
        let upper_bridge = if closed { "le" } else { "lt" };
        Ok(format!("(by\n  {}\n  let _range := {range}\n  let _point := {point}\n  obtain ⟨_lower, _lower_eq⟩ := (M.integer_members _).mp _range.wd.1\n  obtain ⟨_upper, _upper_eq⟩ := (M.integer_members _).mp _range.wd.2\n  obtain ⟨_index, _index_eq⟩ := (M.integer_members _).mp {integer}\n  have _lower_real : (_lower : ℝ) ≤ (_index : ℝ) := (Litex.NativeBridge.le_iff_ofDenoteReal _range.val.start _point (_lower : ℝ) (_index : ℝ) (by simpa only [Complex.ofReal_intCast] using _lower_eq) (by simpa only [Complex.ofReal_intCast] using _index_eq)).mp {lower}\n  have _upper_real : (_index : ℝ) {relation} (_upper : ℝ) := (Litex.NativeBridge.{upper_bridge}_iff_ofDenoteReal _point _range.val.finish (_index : ℝ) (_upper : ℝ) (by simpa only [Complex.ofReal_intCast] using _index_eq) (by simpa only [Complex.ofReal_intCast] using _upper_eq)).mp {upper}\n  exact Litex.in{family}OfDenote _range.val.start _range.val.finish _point _range.wd.1 _range.wd.2 _lower _upper _index _lower_eq _upper_eq _index_eq (by exact_mod_cast _lower_real) (by exact_mod_cast _upper_real))", definitions.join("\n").replace('\n', "\n  ")))
    }

    pub(in crate::compile_to_lean) fn compile_nonzero_product(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "Product nonzero evidence has another fact family.",
                ))
            }
        };
        let (expression, reversed) = if is_zero(&goal.right) {
            (&goal.left, false)
        } else if is_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Subject",
                "The product guard does not compare with zero.",
            ));
        };
        let product = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "The certified nonzero object is not a product.",
                ))
            }
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Requirements",
                "The product needs two ordered factor proofs.",
            ));
        }
        let mut compiled = Vec::new();
        for ((requirement, proof), child) in requirements
            .iter()
            .zip(proofs)
            .zip([product.left.as_ref(), product.right.as_ref()])
        {
            ensure_nonzero_subject(requirement, child)?;
            let proved = self.compile_verify(proof, position)?;
            if &source_subject(proof)? != requirement {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/RequirementSubject",
                    "A factor proof differs from its ordered requirement.",
                ));
            }
            let native = self.compile_numeric_observation(child, position)?;
            compiled.push(format!(
                "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} {})",
                self.compile_object_reference(child, position)?,
                native.0,
                native.1,
                proved.1
            ));
        }
        let native = self.compile_numeric_observation(expression, position)?;
        let proof = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number (M := M) (0 : ℂ)) {} (0 : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero {} {}))", self.compile_object_reference(expression, position)?, native.0, native.1, compiled[0], compiled[1]);
        Ok(if reversed {
            format!("(fun h => {proof} h.symm)")
        } else {
            proof
        })
    }
}
