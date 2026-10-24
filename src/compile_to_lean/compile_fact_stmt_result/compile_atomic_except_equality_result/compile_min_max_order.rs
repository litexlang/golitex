use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_min_max::min_max_arguments;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::sign_extremum_order::WeakOrderArgumentProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_min_max_bound(
        &self,
        goal: &AtomicFact,
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (extremum, operand) = if maximum { (high, low) } else { (low, high) };
        let Some((a, b)) = min_max_arguments(extremum, maximum) else {
            return Err(LeanCompileError::unsupported("MinMax/BoundConstructor"));
        };
        let component = if operand.ir() == a.ir() {
            1
        } else if operand.ir() == b.ir() {
            2
        } else {
            return Err(LeanCompileError::unsupported("MinMax/BoundOperand"));
        };
        if strict {
            return Err(LeanCompileError::unsupported("MinMax/StrictBound"));
        }
        let law = if maximum {
            "operandsLeMax"
        } else {
            "minLeOperands"
        };
        Ok(format!(
            "(Litex.{law} {}).{component}",
            self.compile_object_reference(extremum, position)?
        ))
    }

    pub(super) fn compile_min_max_monotone(
        &self,
        goal: &AtomicFact,
        maximum: bool,
        left_order: &WeakOrderArgumentProof,
        right_order: &WeakOrderArgumentProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (Some((a, b)), Some((c, d))) = (
            min_max_arguments(low, maximum),
            min_max_arguments(high, maximum),
        ) else {
            return Err(LeanCompileError::unsupported("MinMax/MonotoneConstructors"));
        };
        if strict {
            return Err(LeanCompileError::unsupported("MinMax/StrictMonotonicity"));
        }
        let mut stage = 0;
        let mut premises = Vec::new();
        for (left, right, evidence, field, component) in [
            (a, c, left_order, "left", 1),
            (b, d, right_order, "right", 2),
        ] {
            match evidence {
                WeakOrderArgumentProof::SameArgument(original) => {
                    if left.ir() != right.ir() || original.ir() != left.ir() {
                        return Err(LeanCompileError::unsupported("MinMax/FixedArgument"));
                    }
                    premises.push(format!(
                        "(Litex.leRefl _minmax_left.val.{field} _minmax_left.wd.{component})"
                    ));
                }
                WeakOrderArgumentProof::ByOrder(proof) => {
                    let Fact::AtomicFact(fact) = source_subject(proof)? else {
                        return Err(LeanCompileError::unsupported("MinMax/OrderPremise"));
                    };
                    let (actual_left, actual_right, actual_strict) = source_order_oriented(&fact)?;
                    if actual_strict
                        || actual_left.ir() != left.ir()
                        || actual_right.ir() != right.ir()
                    {
                        return Err(LeanCompileError::unsupported("MinMax/OrderPremise"));
                    }
                    premises.push(
                        self.compile_verify(proof, &position.atomic_search_prior(stage)?)?
                            .1,
                    );
                    stage += 1;
                }
            }
        }
        let complete = position.atomic_search_prior(stage)?;
        Ok(format!(
            "(by\n  let _minmax_left := {}\n  let _minmax_right := {}\n  exact Litex.minMaxMonotone _minmax_left _minmax_right {} {}\n)",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?,
            premises[0],
            premises[1]
        ))
    }
}
