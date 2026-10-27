use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_hyperbolic::hyperbolic_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_hyperbolic_nonzero(
        &self,
        fact: &NotEqualFact,
        kind: &str,
        premise: Option<&VerifyFactResult>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, zero, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((actual, argument)) = hyperbolic_argument(object) else {
                continue;
            };
            if actual != kind || !is_exact_zero(zero) {
                continue;
            }
            let condition = if let Some(premise) = premise {
                if kind != "Sinh"
                    || !matches!(source_subject(premise)?, Fact::AtomicFact(AtomicFact::NotEqualFact(p)) if p.left.ir() == argument.ir() && p.right.ir() == zero.ir())
                {
                    return Err(LeanCompileError::unsupported("Hyperbolic/NonzeroPremise"));
                }
                format!(" {}", self.compile_verify(premise, position)?.1)
            } else {
                if !matches!(kind, "Cosh" | "Sech" | "Coth" | "Csch") {
                    return Err(LeanCompileError::unsupported("Hyperbolic/NonzeroRule"));
                }
                String::new()
            };
            let term = self.compile_object_reference(object, position)?;
            let zero_value = self.compile_numeric_observation(zero, position)?;
            let orientation = if reverse { ".symm" } else { "" };
            return Ok(format!("(fun _same => (Litex.{}Nonzero {term}{condition}) (_same{orientation}.trans (({}).trans (congrArg M.number (by norm_num : {} = (0 : ℂ))))))", kind.to_lowercase(), zero_value.1, zero_value.0));
        }
        Err(LeanCompileError::unsupported("Hyperbolic/NonzeroSubject"))
    }
}
