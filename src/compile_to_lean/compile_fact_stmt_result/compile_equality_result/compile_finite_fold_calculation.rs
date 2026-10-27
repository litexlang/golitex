use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::FiniteSetReduceEvaluationResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_fold_value(
        &self,
        evidence: &FiniteSetReduceEvaluationResult,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String), LeanCompileError> {
        let Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(fold)) = &evidence.source
        else {
            return Err(LeanCompileError::unsupported(
                "FiniteFoldCalculation/Source",
            ));
        };
        let (arguments, enumeration) =
            self.compile_numeric_enumeration(&fold.set, &evidence.enumeration, position)?;
        let seed = self.compile_numeric_observation(&fold.seed, position)?;
        let initial = EvalRational::from_obj(&evidence.seed)
            .ok_or_else(|| LeanCompileError::unsupported("FiniteFoldCalculation/Seed"))?;
        if seed.3.as_ref() != Some(&initial) {
            return Err(LeanCompileError::unsupported("FiniteFoldCalculation/Seed"));
        }
        let (value, steps) = self.compile_fold_steps(
            &evidence.terms,
            &fold.func,
            &fold.op,
            &initial,
            &arguments,
            position,
        )?;
        if EvalRational::from_obj(&evidence.value).as_ref() != Some(&value) {
            return Err(LeanCompileError::unsupported("FiniteFoldCalculation/Value"));
        }
        let source = self.compile_object_reference(&evidence.source, position)?;
        let seed_number = exact_rational_literal(&initial, "ℂ")?;
        let output = exact_rational_literal(&value, "ℂ")?;
        let numbers = arguments
            .iter()
            .map(|n| exact_rational_literal(n, "ℂ"))
            .collect::<Result<Vec<_>, _>>()?;
        let objects = numbers
            .iter()
            .map(|n| format!("M.number {n}"))
            .collect::<Vec<_>>()
            .join(", ");
        let mut lines = vec![format!("let _fold := {source}"),
            format!("have _seed : Litex.denote _fold.val.seed = M.number {seed_number} := ({}).trans (congrArg M.number (by norm_num : {} = {seed_number}))", seed.1, seed.0),
            format!("have _members : ∀ x, M.mem x (Litex.denote _fold.val.set) ↔ x ∈ ([{objects}] : List M.Value) := {enumeration}"),
            format!("have _distinct : ([{objects}] : List M.Value).Nodup := List.Nodup.map M.number_injective (by norm_num : ([{}] : List ℂ).Nodup)", numbers.join(", "))];
        lines.extend(steps);
        let mut rewrites = vec!["_seed".to_string()];
        for i in 0..evidence.terms.len() {
            rewrites.extend([format!("_term_{i}"), format!("_step_{i}")]);
        }
        lines.push(format!(
            "apply (Litex.finiteFoldEnumerate _fold [{objects}] _distinct _members).trans"
        ));
        lines.push(format!("show Litex.foldValue [{objects}] (Litex.denote _fold.val.function) (Litex.denote _fold.val.operation) (Litex.denote _fold.val.seed) = M.number {output}"));
        lines.push(format!(
            "norm_num [Litex.foldValue, Litex.foldApply2, {}]",
            rewrites.join(", ")
        ));
        Ok((
            value,
            format!("(by\n  {})", lines.join("\n").replace('\n', "\n  ")),
        ))
    }
}
