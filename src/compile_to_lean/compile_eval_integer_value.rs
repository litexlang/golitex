use super::helper::*;
use super::source_position::{arithmetic_stages, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FunctionApplicationEvaluationResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef as WD;
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;

impl LitexToLeanCompiler {
    pub(super) fn compile_eval_integer_value(
        &self,
        object: &Obj,
        evaluations: &[FunctionApplicationEvaluationResult],
        remaining: &mut usize,
        aggregates: &[AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let (operation, children) = arithmetic_constructor_pairs(object, object)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerOperation"))?;
        let mut checked = Vec::new();
        for (child, _) in children.iter().rev() {
            checked.push(self.compile_eval_value(
                child,
                evaluations,
                remaining,
                aggregates,
                remaining_aggregates,
                position,
            )?);
        }
        checked.reverse();
        let integers = checked
            .iter()
            .map(|(value, _, _)| {
                value
                    .to_i128_if_integer()
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerArgument"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let args = checked
            .iter()
            .map(|(value, _, _)| {
                ClosedNumericExpr::try_from_obj(&value.to_obj())
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerArgument"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let unary = || Box::new(args[0].clone());
        let binary = || (Box::new(args[0].clone()), Box::new(args[1].clone()));
        let (residual, law) = match operation {
            "factorialValue" => (
                ClosedNumericExpr::Factorial(unary()),
                "factorialValue_number",
            ),
            "gcdValue" => {
                let (a, b) = binary();
                (ClosedNumericExpr::Gcd(a, b), "gcdLcmValue_numbers false")
            }
            "lcmValue" => {
                let (a, b) = binary();
                (ClosedNumericExpr::Lcm(a, b), "gcdLcmValue_numbers true")
            }
            "modValue" => {
                let (a, b) = binary();
                (
                    ClosedNumericExpr::Mod(a, b),
                    "integerDivisionValue_numbers false",
                )
            }
            "quotValue" => {
                let (a, b) = binary();
                (
                    ClosedNumericExpr::Quot(a, b),
                    "integerDivisionValue_numbers true",
                )
            }
            _ => return Err(LeanCompileError::unsupported("Eval/IntegerOperation")),
        };
        // This exact evaluator also validates gcd's nonzero pair, quotient's
        // positive divisor and factorial's natural domain, without coercion.
        let value = EvalRational::from_obj(&residual.to_obj())
            .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactIntegerValue"))?;
        let output = exact_rational_literal(&value, "ℂ")?;
        let ty = if operation == "factorialValue" {
            "ℕ"
        } else {
            "ℤ"
        };
        let native = integers
            .iter()
            .map(|n| format!("({n} : {ty})"))
            .collect::<Vec<_>>()
            .join(" ");
        let op = arithmetic_operation_term(operation);
        let congruence = match checked.as_slice() {
            [(_, p, _)] => format!("(congrArg {op} {p})"),
            [(_, p, _), (_, q, _)] => format!("(congrArg₂ {op} {p} {q})"),
            _ => return Err(LeanCompileError::unsupported("Eval/IntegerArity")),
        };
        let raw = self.compile_normalization_value(object, position)?;
        let proof = format!("(show {raw} = M.number {output} from {congruence}.trans (by\n  have _numeric := Litex.{law} (M := M) {native}\n  norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric\n  exact _numeric))");
        Ok((
            value,
            proof,
            checked.into_iter().flat_map(|(_, _, ids)| ids).collect(),
        ))
    }

    /// Closed eval omits carrier searches, but retains each child and the
    /// divisor check. Derive integer carriers from those exact observations.
    pub(super) fn compile_eval_integer_wd(
        &self,
        proof: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if !super::compile_eval_stmt_result::in_closed_eval(position) {
            return Ok(None);
        }
        let DetailedObjWellDefinedProof::ByDef {
            obj,
            proof: ObjWellDefinedProofByDef::IntegerOperator(evidence),
        } = proof.detailed_ref()
        else {
            return Ok(None);
        };
        if ClosedNumericExpr::try_from_obj(obj).is_none() {
            return Ok(None);
        }
        let (operation, args) = arithmetic_constructor_pairs(obj, obj)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerWDObject"))?;
        let name = match (operation, evidence) {
            ("factorialValue", WD::Factorial(_)) => "factorial",
            ("gcdValue", WD::Gcd(_)) => "gcd",
            ("lcmValue", WD::Lcm(_)) => "lcm",
            ("modValue", WD::Mod(_)) => "mod",
            ("quotValue", WD::Quot(_)) => "quot",
            _ => return Err(LeanCompileError::unsupported("Eval/IntegerWDConstructor")),
        };
        let (children, requirements) = arithmetic_stages(proof)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerWDStages"))?;
        let guard_count = usize::from(matches!(name, "mod" | "quot"));
        // Full ordinary WD is consumed by the established constructor branch.
        if requirements.len() > guard_count {
            return Ok(None);
        }
        if children.len() != args.len() || requirements.len() != guard_count {
            return Err(LeanCompileError::unsupported("Eval/IntegerWDStages"));
        }
        let mut terms = Vec::new();
        let mut members = Vec::new();
        let mut denotes = Vec::new();
        let mut integers = Vec::new();
        for (i, ((arg, _), child)) in args.iter().zip(children).enumerate() {
            ensure_object(arg, child)?;
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let term = self.compile_wd(child, &prior)?;
            let observation = self.numeric_wd(child, &prior)?;
            let n = observation
                .3
                .as_ref()
                .and_then(EvalRational::to_i128_if_integer)
                .ok_or_else(|| LeanCompileError::unsupported("Eval/IntegerWDDomain"))?;
            if EvalRational::from_obj(arg).as_ref() != observation.3.as_ref()
                || (name == "factorial" && n < 0)
                || (name == "quot" && i == 1 && n <= 0)
            {
                return Err(LeanCompileError::unsupported("Eval/IntegerWDDomain"));
            }
            let set = if name == "factorial" {
                "N"
            } else if name == "quot" && i == 1 {
                "NPos"
            } else {
                "Z"
            };
            let native_ty = if set == "Z" { "ℤ" } else { "ℕ" };
            let literal = format!("(({n} : {native_ty}) : ℂ)");
            let denote = format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = {literal})))",
                observation.1, observation.0
            );
            let numeric_member = if set == "NPos" {
                format!("(Litex.numberInNPosOfEq {literal} {n} rfl (by norm_num))")
            } else {
                format!("(Litex.NativeBridge.numberIn{set} ({n}))")
            };
            members.push(format!("(Litex.NativeBridge.inOfDenoteNumber {term} {literal} Litex.{set} {denote} {numeric_member})"));
            terms.push(term);
            denotes.push(denote);
            integers.push(n);
        }
        let mut prefix = String::new();
        let guard = if guard_count == 1 {
            ensure_nonzero_subject(&source_subject(&requirements[0])?, args[1].0)?;
            let checked = self.compile_wd_requirement(
                &requirements[0],
                &SourcePosition {
                    before: children.len(),
                    ..*position
                },
            )?;
            // Quot needs the stronger positive membership, but its recorded
            // nonzero proof is still checked, not dropped from the replay.
            prefix = format!("let _eval_divisor_nonzero := {checked};\n");
            " _eval_divisor_nonzero".to_string()
        } else if name == "gcd" {
            let i = if integers[0] != 0 {
                0
            } else if integers[1] != 0 {
                1
            } else {
                return Err(LeanCompileError::unsupported("Eval/GcdZeroPair"));
            };
            format!(" (Or.{} (Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number 0) (({} : ℤ) : ℂ) 0 {} rfl (by norm_num)))", if i==0 {"inl"} else {"inr"}, terms[i], integers[i], denotes[i])
        } else {
            String::new()
        };
        let mut constructor = terms;
        constructor.extend(members);
        Ok(Some(format!(
            "({prefix}Litex.{name} {}{})",
            constructor.join(" "),
            if name == "quot" { "" } else { &guard }
        )))
    }
}
