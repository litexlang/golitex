use crate::compile_to_lean::helper::{is_exact_zero, source_order_oriented, source_subject};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_log_algebra(
        &self,
        fact: &EqualFact,
        rule: &EqualitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use EqualitySearchProofByBuiltinRule as Rule;
        match rule {
            Rule::LogProduct(p) => self.compile_log_binary_algebra(
                fact,
                false,
                &p.base_proof,
                [
                    &p.left_argument_positive_proof,
                    &p.right_argument_positive_proof,
                ],
                position,
            ),
            Rule::LogQuotient(p) => self.compile_log_binary_algebra(
                fact,
                true,
                &p.base_proof,
                [&p.numerator_positive_proof, &p.denominator_positive_proof],
                position,
            ),
            Rule::LogReciprocal(p) => self.compile_log_reciprocal_algebra(
                fact,
                &p.base_proof,
                &p.argument_positive_proof,
                position,
            ),
            Rule::LogChangeOfBase(p) => self.compile_log_change_base(
                fact,
                &p.base_proof,
                &p.chosen_base_proof,
                &p.argument_positive_proof,
                position,
            ),
            Rule::LogArgPower(p) => self.compile_log_argument_power(
                fact,
                &p.base_proof,
                &p.argument_positive_proof,
                position,
            ),
            Rule::LogBasePower(p) => self.compile_log_base_power(
                fact,
                &p.base_proof,
                [
                    &p.exponent_real,
                    &p.exponent_nonzero,
                    &p.argument_positive_proof,
                ],
                position,
            ),
            _ => Err(invalid("Rule")),
        }
    }

    fn compile_log_positive_child(
        &self,
        proof: &VerifyFactResult,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(fact) = source_subject(proof)? else {
            return Err(invalid("PositiveFamily"));
        };
        let (zero, subject, strict) = source_order_oriented(&fact)?;
        if !strict || !is_exact_zero(zero) || subject.ir() != object.ir() {
            return Err(invalid("PositiveSubject"));
        }
        Ok(self.compile_verify(proof, position)?.1)
    }

    fn compile_log_binary_algebra(
        &self,
        fact: &EqualFact,
        quotient: bool,
        base: &LogAlgebraBaseProof,
        children: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reverse) in orientations(fact) {
            let Some(log) = log(object) else {
                continue;
            };
            let (a, b) = match (&*log.arg, quotient) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)), false) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Div(p)), true) => (&p.left, &p.right),
                _ => continue,
            };
            let (left, right) = match (other, quotient) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), false) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)), true) => (&p.left, &p.right),
                _ => continue,
            };
            let (Some(left), Some(right)) = (self::log(left), self::log(right)) else {
                continue;
            };
            if left.base.ir() != log.base.ir()
                || right.base.ir() != log.base.ir()
                || left.arg.ir() != a.ir()
                || right.arg.ir() != b.ir()
            {
                continue;
            }
            let guard = self.compile_log_guard(&log.base, base, position)?;
            let ha = self.compile_log_positive_child(children[0], a, position)?;
            let hb = self.compile_log_positive_child(children[1], b, position)?;
            let law = if quotient {
                "logarithmQuotientBaseValue"
            } else {
                "logarithmProductBaseValue"
            };
            return Ok(format!("(let _base_logs := {}; (Litex.{law} _base_logs.val.left _base_logs.val.right (by rfl) {guard} {ha} {hb}){})",self.compile_object_reference(other,position)?,if reverse {".symm"}else{""}));
        }
        Err(invalid("BinaryEndpoints"))
    }

    fn compile_log_reciprocal_algebra(
        &self,
        fact: &EqualFact,
        base: &LogAlgebraBaseProof,
        positive: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reverse) in orientations(fact) {
            let (Some(log), Obj::ArithmeticOperator(ArithmeticOperator::Sub(negative))) =
                (log(object), other)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Div(reciprocal)) = &*log.arg else {
                continue;
            };
            let Some(original) = self::log(&negative.right) else {
                continue;
            };
            if !is_exact_zero(&negative.left)
                || !is_one(&reciprocal.left)
                || original.base.ir() != log.base.ir()
                || original.arg.ir() != reciprocal.right.ir()
            {
                continue;
            }
            let guard = self.compile_log_guard(&log.base, base, position)?;
            let positive =
                self.compile_log_positive_child(positive, &reciprocal.right, position)?;
            return Ok(format!(
                "(Litex.logarithmReciprocalValue {} {guard} {positive}){}",
                self.compile_object_reference(&negative.right, position)?,
                if reverse { ".symm" } else { "" }
            ));
        }
        Err(invalid("ReciprocalEndpoints"))
    }

    fn compile_log_change_base(
        &self,
        fact: &EqualFact,
        base: &LogAlgebraBaseProof,
        chosen: &LogAlgebraBaseProof,
        positive: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reverse) in orientations(fact) {
            let (Some(log), Obj::ArithmeticOperator(ArithmeticOperator::Div(ratio))) =
                (log(object), other)
            else {
                continue;
            };
            let (Some(num), Some(den)) = (self::log(&ratio.left), self::log(&ratio.right)) else {
                continue;
            };
            if num.base.ir() != den.base.ir()
                || num.arg.ir() != log.arg.ir()
                || den.arg.ir() != log.base.ir()
            {
                continue;
            }
            let guard = self.compile_log_guard(&log.base, base, position)?;
            let chosen = self.compile_log_guard(&num.base, chosen, position)?;
            let positive = self.compile_log_positive_child(positive, &log.arg, position)?;
            return Ok(format!("(let _change_logs := {}; (Litex.logarithmChangeBaseValue _change_logs.val.left _change_logs.val.right (by rfl) {guard} {chosen} {positive}){})",self.compile_object_reference(other,position)?,if reverse {".symm"}else{""}));
        }
        Err(invalid("ChangeBaseEndpoints"))
    }

    fn compile_log_argument_power(
        &self,
        fact: &EqualFact,
        base: &LogAlgebraBaseProof,
        positive: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reverse) in orientations(fact) {
            let (Some(log), Obj::ArithmeticOperator(ArithmeticOperator::Mul(weighted))) =
                (log(object), other)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &*log.arg else {
                continue;
            };
            let Some(original) = self::log(&weighted.right) else {
                continue;
            };
            if power.exponent.ir() != weighted.left.ir()
                || original.base.ir() != log.base.ir()
                || original.arg.ir() != power.base.ir()
            {
                continue;
            }
            let guard = self.compile_log_guard(&log.base, base, position)?;
            let positive = self.compile_log_positive_child(positive, &power.base, position)?;
            // The actual parent PowObj WD supplies its supported integer
            // exponent; no integer Verify result is synthesized for this rule.
            return Ok(format!("(let _power_log := {}; let _weighted_log := {}; (Litex.logarithmArgumentPowerValue _power_log.val.arg _weighted_log.val.right (by rfl) {guard} {positive}){})",self.compile_object_reference(object,position)?,self.compile_object_reference(other,position)?,if reverse {".symm"}else{""}));
        }
        Err(invalid("ArgumentPowerEndpoints"))
    }

    fn compile_log_base_power(
        &self,
        fact: &EqualFact,
        base: &LogAlgebraBaseProof,
        children: [&VerifyFactResult; 3],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reverse) in orientations(fact) {
            let (Some(log), Obj::ArithmeticOperator(ArithmeticOperator::Div(ratio))) =
                (log(object), other)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &*log.base else {
                continue;
            };
            let Some(original) = self::log(&ratio.left) else {
                continue;
            };
            if original.base.ir() != power.base.ir()
                || original.arg.ir() != log.arg.ir()
                || ratio.right.ir() != power.exponent.ir()
            {
                continue;
            }
            if !matches!(source_subject(children[0])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==power.exponent.ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("OriginalExponentReal"));
            }
            if !matches!(source_subject(children[1])?,Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==power.exponent.ir() && is_exact_zero(&f.right))
            {
                return Err(invalid("OriginalExponentNonzero"));
            }
            let guard = self.compile_log_guard(&power.base, base, position)?;
            let real = self.compile_verify(children[0], position)?.1;
            let nonzero = self.compile_verify(children[1], position)?.1;
            let positive = self.compile_log_positive_child(children[2], &log.arg, position)?;
            return Ok(format!("(let _power_log := {}; let _quotient_log := {}; (Litex.logarithmBasePowerValue _power_log.val.base _quotient_log.val.left (by rfl) {guard} {real} {nonzero} {positive}){})",self.compile_object_reference(object,position)?,self.compile_object_reference(other,position)?,if reverse {".symm"}else{""}));
        }
        Err(invalid("BasePowerEndpoints"))
    }
}

fn log(object: &Obj) -> Option<&Log> {
    match object {
        Obj::ExpLogOperator(ExpLogOperator::Log(log)) => Some(log),
        _ => None,
    }
}
fn is_one(object: &Obj) -> bool {
    matches!(object,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
}
fn orientations(fact: &EqualFact) -> [(&Obj, &Obj, bool); 2] {
    [
        (&fact.left, &fact.right, false),
        (&fact.right, &fact.left, true),
    ]
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("LogAlgebra/{part}"))
}
