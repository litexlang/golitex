use super::helper::*;
use super::source_position::{arithmetic_stages, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Check the exact scalar endpoint with numeric semantic laws.
    pub(super) fn compile_eval_closed_value(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String), LeanCompileError> {
        let (value, proof, _) =
            self.compile_eval_value(object, &[], &mut 0, &[], &mut 0, position)?;
        Ok((value, proof))
    }

    /// Reverse traversal consumes the evaluator's postorder call records.
    /// Returned citation IDs retain forward execution order.
    pub(super) fn compile_eval_value(
        &self,
        object: &Obj,
        evaluations: &[crate::execute::execute_eval_stmt::aggregate_evaluation_result::FunctionApplicationEvaluationResult],
        remaining: &mut usize,
        aggregates: &[crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        if matches!(object, Obj::FnObj(_)) {
            return self.compile_eval_function_value(
                object,
                evaluations,
                remaining,
                aggregates,
                remaining_aggregates,
                position,
            );
        }
        if matches!(object, Obj::IteratedOperator(_)) {
            return self.compile_eval_aggregate_value(
                object,
                aggregates,
                remaining_aggregates,
                position,
            );
        }
        let raw = self.compile_normalization_value(object, position)?;
        let (value, proof, cites) = match object {
            Obj::Literal(Literal::Number(n)) => {
                let value = EvalRational::from_obj(object)
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactScalar"))?;
                let literal = exact_rational_literal(&value, "ℂ")?;
                (
                    value,
                    format!(
                        "(congrArg M.number (show {} = {literal} from by norm_num))",
                        number_literal(n, "ℂ")?
                    ),
                    vec![],
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => {
                let (a, p, cites) = self.compile_eval_value(
                    &n.arg,
                    evaluations,
                    remaining,
                    aggregates,
                    remaining_aggregates,
                    position,
                )?;
                let value = EvalRational::new(0, 1)
                    .unwrap()
                    .sub(&a)
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactScalar"))?;
                let a = exact_rational_literal(&a, "ℂ")?;
                (value, format!("((congrArg M.negValue {p}).trans ((M.neg_numbers {a}).trans (congrArg M.number (by norm_num))))"), cites)
            }
            Obj::ArithmeticOperator(op) => {
                let (a, b, name) = match op {
                    ArithmeticOperator::Add(p) => (&p.left, &p.right, "add"),
                    ArithmeticOperator::Sub(p) => (&p.left, &p.right, "sub"),
                    ArithmeticOperator::Mul(p) => (&p.left, &p.right, "mul"),
                    ArithmeticOperator::Div(p) => (&p.left, &p.right, "div"),
                    ArithmeticOperator::Pow(p) => (&p.base, &p.exponent, "pow"),
                    _ => return Err(LeanCompileError::unsupported("Eval/ScalarOperator")),
                };
                let (bv, bp, right_cites) = self.compile_eval_value(
                    b,
                    evaluations,
                    remaining,
                    aggregates,
                    remaining_aggregates,
                    position,
                )?;
                let (av, ap, mut cites) = self.compile_eval_value(
                    a,
                    evaluations,
                    remaining,
                    aggregates,
                    remaining_aggregates,
                    position,
                )?;
                cites.extend(right_cites);
                let value = match name {
                    "add" => av.add(&bv),
                    "sub" => av.sub(&bv),
                    "mul" => av.mul(&bv),
                    "div" => av.div(&bv),
                    "pow" => bv.to_i128_if_integer().and_then(|n| av.pow_integer(n)),
                    _ => unreachable!(),
                }
                .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactScalar"))?;
                let al = exact_rational_literal(&av, "ℂ")?;
                let bl = exact_rational_literal(&bv, "ℂ")?;
                let law = match name {
                    "div" => format!("(M.div_numbers {al} {bl} (by norm_num))"),
                    "pow" => {
                        let n = bv
                            .to_i128_if_integer()
                            .ok_or_else(|| LeanCompileError::unsupported("Eval/PowerExponent"))?;
                        if n >= 0 {
                            format!("(M.pow_numbers_nat {al} {n})")
                        } else {
                            format!("(show M.powValue (M.number {al}) (M.number {bl}) = M.number ({al} ^ ({n} : ℤ)) from by simpa only [Int.cast_neg, Int.cast_ofNat] using M.pow_numbers_int {al} ({n}) (by norm_num))")
                        }
                    }
                    _ => format!("(M.{name}_numbers {al} {bl})"),
                };
                (value, format!("((congrArg₂ M.{name}Value {ap} {bp}).trans ({law}.trans (congrArg M.number (by norm_num))))"), cites)
            }
            _ => return Err(LeanCompileError::unsupported("Eval/ScalarOperator")),
        };
        let literal = exact_rational_literal(&value, "ℂ")?;
        Ok((
            value,
            format!("(show {raw} = M.number {literal} from {proof})"),
            cites,
        ))
    }

    /// Eval's closed numeric WD deliberately omits recursively searched carrier
    /// proofs. Reconstruct owned objects from their original child WD; certify
    /// carriers from exact numeric denotations only in that original context.
    pub(super) fn compile_eval_closed_wd(
        &self,
        proof: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if !super::compile_eval_stmt_result::in_closed_eval(position) {
            return Ok(None);
        }
        let ObjWellDefinedProof::ByDef {
            obj: object,
            proof: ObjWellDefinedProofByDef::ArithmeticOperator(evidence),
        } = proof
        else {
            return Ok(None);
        };
        let (children, requirements) = arithmetic_stages(proof)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/WDStages"))?;
        let (args, name): (Vec<&Obj>, &str) = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => (vec![&p.left, &p.right], "add"),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => (vec![&p.left, &p.right], "sub"),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => (vec![&p.left, &p.right], "mul"),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => (vec![&p.left, &p.right], "div"),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
                (vec![&p.base, &p.exponent], "pow")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => (vec![&p.arg], "neg"),
            _ => return Ok(None),
        };
        use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ArithmeticOperatorObjWellDefinedProofByDef as WD;
        if !matches!(
            (name, evidence),
            ("add", WD::Add(_))
                | ("sub", WD::Sub(_))
                | ("mul", WD::Mul(_))
                | ("div", WD::Div(_))
                | ("neg", WD::Neg(_))
                | ("pow", WD::Pow(_))
        ) {
            return Err(LeanCompileError::unsupported("Eval/WDConstructor"));
        }
        if !requirements.is_empty() && !(name == "div" && requirements.len() == 1) {
            return Ok(None);
        }
        if children.len() != args.len() || requirements.len() != usize::from(name == "div") {
            return Err(LeanCompileError::unsupported("Eval/WDStages"));
        }
        let mut terms = Vec::new();
        let mut members = Vec::new();
        let mut values = Vec::new();
        let mut denotes = Vec::new();
        for (i, (arg, child)) in args.iter().zip(children).enumerate() {
            ensure_object(arg, child)?;
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let term = self.compile_wd(child, &prior)?;
            let (v, p) = self.compile_eval_closed_value(arg, &prior)?;
            let l = exact_rational_literal(&v, "ℂ")?;
            members.push(format!("(Litex.NativeBridge.inOfDenoteNumber {term} {l} Litex.C {p} (Litex.numberInC {l}))"));
            terms.push(term);
            values.push(v);
            denotes.push(p);
        }
        let term = match name {
            "neg" => format!("(Litex.neg {} {})", terms[0], members[0]),
            "pow" => {
                let n = values[1]
                    .to_i128_if_integer()
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/PowerExponent"))?;
                let set = if n >= 0 { "N" } else { "Z" };
                let kind = if n >= 0 { "Nat" } else { "Int" };
                let ty = if n >= 0 { "ℕ" } else { "ℤ" };
                let exponent_value = exact_rational_literal(&values[1], "ℂ")?;
                let exponent=format!("(show Litex.Same {} (Litex.number (({n} : {ty}) : ℂ)) from ({}).trans (congrArg M.number (show {exponent_value} = (({n} : {ty}) : ℂ) from by norm_num)))",terms[1],denotes[1]);
                let member=format!("(Litex.NativeBridge.inOfDenoteNumber {} (({n} : {ty}) : ℂ) Litex.{set} {exponent} (Litex.NativeBridge.numberIn{set} ({n})))",terms[1]);
                let guard = if n < 0 {
                    let v = exact_rational_literal(&values[0], "ℂ")?;
                    format!(" (Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number 0) {v} 0 {} rfl (by norm_num))",terms[0],denotes[0])
                } else {
                    String::new()
                };
                format!(
                    "(Litex.pow{kind} {} {} ({n}) {} {member}{guard} {exponent})",
                    terms[0], terms[1], members[0]
                )
            }
            "div" => {
                ensure_nonzero_subject(&source_subject(&requirements[0])?, args[1])?;
                let p = self.compile_wd_requirement(
                    &requirements[0],
                    &SourcePosition {
                        before: children.len(),
                        ..*position
                    },
                )?;
                format!(
                    "(Litex.div {} {} {} {} {p})",
                    terms[0], terms[1], members[0], members[1]
                )
            }
            _ => format!(
                "(Litex.{name} {} {} {} {})",
                terms[0], terms[1], members[0], members[1]
            ),
        };
        Ok(Some(term))
    }
}
