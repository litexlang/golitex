//! Replay exact radical evaluation through checked numeric denotations.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecEvalStmtSuccess;
use crate::prelude::*;
use crate::rational_expression::exact_radical::ExactRadical;
use std::collections::BTreeMap;

/// Only linear combinations and rational scaling are supported here. Products
/// of two irrational roots need a separate checked multiplication certificate.
fn linear_radical(object: &Obj, roots: &mut Vec<Obj>) -> bool {
    if EvalRational::from_obj(object).is_some() {
        return true;
    }
    match object {
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) => {
            let Some(radicand) = EvalRational::from_obj(&root.arg) else {
                return false;
            };
            if radicand.is_negative() || ExactRadical::from_obj(object).is_none() {
                return false;
            }
            if !roots.iter().any(|old| old.ir() == object.ir()) {
                roots.push(object.clone());
            }
            true
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => linear_radical(&p.arg, roots),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
            linear_radical(&p.left, roots) && linear_radical(&p.right, roots)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            linear_radical(&p.left, roots) && linear_radical(&p.right, roots)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
            (EvalRational::from_obj(&p.left).is_some()
                || EvalRational::from_obj(&p.right).is_some())
                && linear_radical(&p.left, roots)
                && linear_radical(&p.right, roots)
        }
        _ => false,
    }
}

/// Produce a small Lean certificate for the canonical form of one square root.
fn root_certificate(
    root: &Obj,
    index: usize,
) -> Result<Option<(String, String)>, LeanCompileError> {
    let Obj::ExpLogOperator(ExpLogOperator::Sqrt(original)) = root else {
        return Err(LeanCompileError::unsupported("Eval/RadicalRoot"));
    };
    let radicand = EvalRational::from_obj(&original.arg)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalRadicand"))?;
    let canonical = ExactRadical::from_obj(root)
        .and_then(|r| r.checked_to_obj())
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalCanonical"))?;
    if canonical.ir() == root.ir() {
        return Ok(None);
    }
    let (coefficient, squarefree) = match &canonical {
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) => (EvalRational::new(1, 1).unwrap(), &*r.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) => {
            let c = EvalRational::from_obj(&m.left)
                .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalCoefficient"))?;
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) = &*m.right else {
                return Err(LeanCompileError::unsupported("Eval/RadicalCanonicalRoot"));
            };
            (c, &*r.arg)
        }
        _ => return Err(LeanCompileError::unsupported("Eval/RadicalCanonicalRoot")),
    };
    let squarefree = EvalRational::from_obj(squarefree)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalSquarefree"))?;
    if coefficient.is_negative() || squarefree.is_negative() {
        return Err(LeanCompileError::unsupported("Eval/RadicalSign"));
    }
    let r = exact_rational_literal(&radicand, "ℝ")?;
    let c = exact_rational_literal(&coefficient, "ℝ")?;
    let d = exact_rational_literal(&squarefree, "ℝ")?;
    let name = format!("_litex_radical_{index}");
    let proof = format!("have {name} : Real.sqrt {r} = {c} * Real.sqrt {d} := by\n  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr\n  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ {d} by norm_num)]");
    Ok(Some((name, proof)))
}

/// A direct product of two nonnegative rational square roots has one exact
/// radical term. Lean independently checks both its sign and its square.
fn root_product_certificate(
    object: &Obj,
    output: &Obj,
) -> Result<Option<String>, LeanCompileError> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = object else {
        return Ok(None);
    };
    let (
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(b)),
    ) = (&*product.left, &*product.right)
    else {
        return Ok(None);
    };
    let a = EvalRational::from_obj(&a.arg)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductInput"))?;
    let b = EvalRational::from_obj(&b.arg)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductInput"))?;
    if a.is_negative() || b.is_negative() {
        return Err(LeanCompileError::unsupported("Eval/RadicalProductSign"));
    }
    let (value, square) = if let Some(q) = EvalRational::from_obj(output) {
        (exact_rational_literal(&q, "ℝ")?, "norm_num".to_owned())
    } else {
        let (coefficient, root) = match output {
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) => (EvalRational::new(1, 1).unwrap(), r),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) => {
                let c = EvalRational::from_obj(&m.left).ok_or_else(|| {
                    LeanCompileError::unsupported("Eval/RadicalProductCoefficient")
                })?;
                let Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) = &*m.right else {
                    return Err(LeanCompileError::unsupported("Eval/RadicalProductOutput"));
                };
                (c, r)
            }
            _ => return Err(LeanCompileError::unsupported("Eval/RadicalProductOutput")),
        };
        if coefficient.is_negative() {
            return Err(LeanCompileError::unsupported("Eval/RadicalProductSign"));
        }
        let d = EvalRational::from_obj(&root.arg)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductOutput"))?;
        if d.is_negative() {
            return Err(LeanCompileError::unsupported("Eval/RadicalProductSign"));
        }
        let is_one = coefficient == EvalRational::new(1, 1).unwrap();
        let c = exact_rational_literal(&coefficient, "ℝ")?;
        let d = exact_rational_literal(&d, "ℝ")?;
        (
            if is_one {
                format!("Real.sqrt {d}")
            } else {
                format!("{c} * Real.sqrt {d}")
            },
            format!("nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ {d} by norm_num)]"),
        )
    };
    let a = exact_rational_literal(&a, "ℝ")?;
    let b = exact_rational_literal(&b, "ℝ")?;
    Ok(Some(format!("have _litex_product : Real.sqrt {a} * Real.sqrt {b} = {value} := by\n  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ {a})]\n  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr\n  {square}\nexact_mod_cast _litex_product")))
}

/// Verify each pair in the evaluator's product of two canonical linear sums.
/// The final linear combination checks their coefficients in Lean as well.
fn radical_sum_product_certificate(
    left: &Obj,
    right: &Obj,
) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
    let left = ExactRadical::from_obj(left)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductLeft"))?;
    let right = ExactRadical::from_obj(right)
        .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductRight"))?;
    let mut weighted_pairs: BTreeMap<(i128, i128), EvalRational> = BTreeMap::new();
    for (a, ca) in left.terms().filter(|(a, _)| *a != 1) {
        for (b, cb) in right.terms().filter(|(b, _)| *b != 1) {
            let key = (a.min(b), a.max(b));
            let coefficient = ca
                .mul(cb)
                .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductCoefficient"))?;
            let value = match weighted_pairs.get(&key) {
                Some(previous) => previous.add(&coefficient).ok_or_else(|| {
                    LeanCompileError::unsupported("Eval/RadicalProductCoefficient")
                })?,
                None => coefficient,
            };
            if value.is_zero() {
                weighted_pairs.remove(&key);
            } else {
                weighted_pairs.insert(key, value);
            }
        }
    }
    // Each pair emits a Lean proof; do not let a single source step generate
    // an unbounded number of certificates.
    if weighted_pairs.len() > 64 {
        return Err(LeanCompileError::unsupported("Eval/RadicalProductBudget"));
    }
    let mut proofs = Vec::new();
    let mut combination = Vec::new();
    for ((a, b), coefficient) in weighted_pairs {
        let root = |n: i128| {
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
                arg: Box::new(Obj::Literal(Literal::Number(Number::new(n.to_string())))),
            }))
        };
        let pair = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(root(a)),
            right: Box::new(root(b)),
        }));
        let result = ExactRadical::from_obj(&pair)
            .and_then(|r| r.checked_to_obj())
            .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductPair"))?;
        let result_complex = if let Some(q) = EvalRational::from_obj(&result) {
            exact_rational_literal(&q, "ℂ")?
        } else {
            let (c, d) = match &result {
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) => {
                    (EvalRational::new(1, 1).unwrap(), &*r.arg)
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) => {
                    let c = EvalRational::from_obj(&m.left).ok_or_else(|| {
                        LeanCompileError::unsupported("Eval/RadicalProductCoefficient")
                    })?;
                    let Obj::ExpLogOperator(ExpLogOperator::Sqrt(r)) = &*m.right else {
                        return Err(LeanCompileError::unsupported("Eval/RadicalProductOutput"));
                    };
                    (c, &*r.arg)
                }
                _ => return Err(LeanCompileError::unsupported("Eval/RadicalProductOutput")),
            };
            let d = EvalRational::from_obj(d)
                .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductOutput"))?;
            let d = exact_rational_literal(&d, "ℝ")?;
            let root = format!("((Real.sqrt {d} : ℝ) : ℂ)");
            if c == EvalRational::new(1, 1).unwrap() {
                root
            } else {
                format!("({} * {root})", exact_rational_literal(&c, "ℂ")?)
            }
        };
        let a_real = exact_rational_literal(&EvalRational::new(a, 1).unwrap(), "ℝ")?;
        let b_real = exact_rational_literal(&EvalRational::new(b, 1).unwrap(), "ℝ")?;
        let body = root_product_certificate(&pair, &result)?
            .ok_or_else(|| LeanCompileError::unsupported("Eval/RadicalProductPair"))?;
        let name = format!("_litex_pair_{}", proofs.len());
        proofs.push(format!("have {name} : ((Real.sqrt {a_real} : ℝ) : ℂ) * ((Real.sqrt {b_real} : ℝ) : ℂ) = {result_complex} := by\n  {}", body.replace('\n', "\n  ")));
        combination.push(format!(
            "{} * {name}",
            exact_rational_literal(&coefficient, "ℂ")?
        ));
    }
    Ok((proofs, combination))
}

impl LitexToLeanCompiler {
    /// Interpret a closed rewrite endpoint as a semantic value. This internal
    /// value is not a newly formed Litex object and needs no invented WD.
    fn linear_radical_observation(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if EvalRational::from_obj(object).is_some() {
            let (value, proof) = self.compile_eval_closed_value(object, position)?;
            return Ok((exact_rational_literal(&value, "ℂ")?, proof));
        }
        if let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = object {
            let (value, proof) = self.compile_eval_closed_value(&root.arg, position)?;
            if value.is_negative() {
                return Err(LeanCompileError::unsupported("Eval/RadicalSign"));
            }
            let real = exact_rational_literal(&value, "ℝ")?;
            let complex = exact_rational_literal(&value, "ℂ")?;
            let cast = format!("(by norm_num : {complex} = (({real} : ℝ) : ℂ))");
            let result = format!("((Real.sqrt {real} : ℝ) : ℂ)");
            let denotation = format!("((congrArg (Litex.sqrtValue (M := M)) {proof}).trans ((congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) {cast}).trans (Litex.sqrtValue_number (M := M) {real})))");
            return Ok((result, denotation));
        }
        let (children, operation, symbol) = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => (vec![&*p.arg], "neg", "-"),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                (vec![&*p.left, &*p.right], "add", "+")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                (vec![&*p.left, &*p.right], "sub", "-")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                (vec![&*p.left, &*p.right], "mul", "*")
            }
            _ => return Err(LeanCompileError::unsupported("Eval/LinearRadicalOperator")),
        };
        let observed = children
            .iter()
            .map(|child| self.linear_radical_observation(child, position))
            .collect::<Result<Vec<_>, _>>()?;
        match observed.as_slice() {
            [(value, proof)] => Ok((format!("(-{value})"),
                format!("((congrArg M.negValue {proof}).trans (M.neg_numbers {value}))"))),
            [(a, pa), (b, pb)] => Ok((format!("({a} {symbol} {b})"),
                format!("((congrArg₂ M.{operation}Value {pa} {pb}).trans (M.{operation}_numbers {a} {b}))"))),
            _ => Err(LeanCompileError::unsupported("Eval/LinearRadicalArity")),
        }
    }

    pub(super) fn compile_eval_linear_radical(
        &self,
        p: &ExecEvalStmtSuccess,
        rewritten: &str,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if !p.function_evaluations.is_empty() || !p.aggregate_evaluations.is_empty() {
            return Err(LeanCompileError::unsupported("Eval/RadicalEvidence"));
        }
        let canonical = ExactRadical::from_obj(&p.rewritten_object)
            .and_then(|r| r.checked_to_obj())
            .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactRadical"))?;
        if canonical.ir() != p.evaluated_object.ir() {
            return Err(LeanCompileError::unsupported("Eval/RadicalValue"));
        }
        let product = root_product_certificate(&p.rewritten_object, &p.evaluated_object)?;
        let mut roots = Vec::new();
        let mut pairs = None;
        if product.is_none() && !linear_radical(&p.rewritten_object, &mut roots) {
            roots.clear();
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = &p.rewritten_object else {
                return Err(LeanCompileError::unsupported("Eval/LinearRadicalDomain"));
            };
            if !linear_radical(&m.left, &mut roots) || !linear_radical(&m.right, &mut roots) {
                return Err(LeanCompileError::unsupported("Eval/LinearRadicalDomain"));
            }
            pairs = Some(radical_sum_product_certificate(&m.left, &m.right)?);
        }
        if product.is_none() && !linear_radical(&p.evaluated_object, &mut roots) {
            return Err(LeanCompileError::unsupported("Eval/LinearRadicalDomain"));
        }
        let mut names = Vec::new();
        let mut certificates = Vec::new();
        for (i, root) in roots.iter().enumerate() {
            if let Some((name, proof)) = root_certificate(root, i)? {
                names.push(name);
                certificates.push(proof);
            }
        }
        let combination = if let Some((pair_proofs, combination)) = pairs {
            certificates.extend(pair_proofs);
            combination
        } else {
            Vec::new()
        };
        let evaluated = SourcePosition {
            before: 2,
            ..*position
        };
        let wd = &p.evaluated_equal_well_defined;
        let bindings = self.compile_equal_wd_locals(&p.evaluated_equal_fact, wd, &evaluated)?;
        let formed = SourcePosition::new(Some(&evaluated), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self.compile_object_reference(&p.source_object, &formed)?;
        let right = self.compile_object_reference(&p.evaluated_object, &formed)?;
        let source_denotation = self.compile_normalization_denotation(&p.source_object, &formed)?;
        let result_denotation =
            self.compile_normalization_denotation(&p.evaluated_object, &formed)?;
        let (left_value, left_proof) =
            self.linear_radical_observation(&p.rewritten_object, &formed)?;
        let (right_value, right_proof) =
            self.linear_radical_observation(&p.evaluated_object, &formed)?;
        let mut calculation = certificates.join("\n");
        if !calculation.is_empty() {
            calculation.push('\n');
        }
        if !names.is_empty() {
            calculation.push_str(&format!("rw [{}]\n", names.join(", ")));
        }
        if !names.is_empty() {
            calculation.push_str("push_cast\n");
        }
        if combination.is_empty() {
            calculation.push_str("ring");
        } else {
            calculation.push_str(&format!("linear_combination {}", combination.join(" + ")));
        }
        if let Some(product) = product {
            calculation = product;
        }
        let native = format!(
            "(by\n  {} : {left_value} = {right_value})",
            calculation.replace('\n', "\n  ")
        );
        let ty = format!("Litex.Same {left} {right}");
        let proof = format!("(show {ty} from ({source_denotation}).trans (({rewritten}).trans (({left_proof}).trans ((congrArg M.number {native}).trans (({right_proof}).symm.trans ({result_denotation}).symm)))))");
        let compiled = (
            Self::scope_equal_wd(ty.clone(), &bindings),
            Self::scope_equal_wd_proof(ty, proof, &bindings),
        );
        let completed = SourcePosition {
            before: 4,
            ..*position
        };
        self.compile_completed_fact_statement(
            &p.evaluated_equal_fact.clone().into(),
            compiled,
            &p.store_and_infer_result,
            &completed,
            index,
            local,
        )
    }
}
