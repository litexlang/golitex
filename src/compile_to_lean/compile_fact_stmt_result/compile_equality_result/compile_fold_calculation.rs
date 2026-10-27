use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{FunctionApplicationEvaluationResult, FunctionApplicationExpansionProof, RangeReduceEvaluationResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_by_aggregate_calculation::AggregateCalculationBuiltinRuleProof;
use crate::prelude::*;
use super::compile_aggregate_calculation::closed_scalar_body;
use super::compile_function_definition::function_head_object;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_range_fold_calculation(
        &self,
        fact: &EqualFact,
        certificate: &AggregateCalculationBuiltinRuleProof,
        evidence: &RangeReduceEvaluationResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::IteratedOperator(IteratedOperator::Reduce(fold)) = &evidence.source else {
            return Err(LeanCompileError::unsupported("FoldCalculation/Source"));
        };
        let (other, reverse) = if fact.left == evidence.source {
            (&fact.right, false)
        } else if fact.right == evidence.source {
            (&fact.left, true)
        } else {
            return Err(LeanCompileError::unsupported("FoldCalculation/Endpoint"));
        };
        let bounds = &evidence.bounds;
        if bounds.start.ir() != fold.start.ir()
            || bounds.end.ir() != fold.end.ir()
            || !bounds.cited_equal_fact_ids.is_empty()
        {
            return Err(LeanCompileError::unsupported("FoldCalculation/Bounds"));
        }
        let first = self.compile_numeric_observation(&fold.start, position)?;
        let last = self.compile_numeric_observation(&fold.end, position)?;
        let seed = self.compile_numeric_observation(&fold.seed, position)?;
        let mut accumulated = EvalRational::from_obj(&evidence.seed)
            .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/SeedValue"))?;
        let count = bounds
            .end_integer
            .checked_sub(bounds.start_integer)
            .and_then(|d| d.checked_add(1))
            .and_then(|d| usize::try_from(d.max(0)).ok());
        if first.3.as_ref().and_then(|n| n.to_i128_if_integer()) != Some(bounds.start_integer)
            || last.3.as_ref().and_then(|n| n.to_i128_if_integer()) != Some(bounds.end_integer)
            || count != Some(evidence.terms.len())
            || seed.3.as_ref() != Some(&accumulated)
        {
            return Err(LeanCompileError::unsupported("FoldCalculation/Enumeration"));
        }
        let source = self.compile_object_reference(&evidence.source, position)?;
        let seed_number = exact_rational_literal(&accumulated, "ℂ")?;
        let mut lines = vec![format!("let _fold := {source}"),
            format!("have _seed : Litex.denote _fold.val.seed = M.number {seed_number} := ({}).trans (congrArg M.number (by norm_num : {} = {seed_number}))", seed.1, seed.0)];
        let mut indices = Vec::new();
        let mut rewrites = vec!["_seed".to_string()];
        for (i, term) in evidence.terms.iter().enumerate() {
            let index = bounds
                .start_integer
                .checked_add(i as i128)
                .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/IndexOverflow"))?;
            let argument = EvalRational::from_obj(&term.argument)
                .filter(|n| n.to_i128_if_integer() == Some(index))
                .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/Argument"))?;
            let term_value = EvalRational::from_obj(&term.term.value)
                .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/TermValue"))?;
            let step_value = EvalRational::from_obj(&term.operation.value)
                .filter(|n| EvalRational::from_obj(&term.accumulated_value).as_ref() == Some(n))
                .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/StepValue"))?;
            let term_proof = self.compile_fold_application_calculation(
                &term.term,
                &fold.func,
                &[&argument],
                position,
            )?;
            let step_proof = self.compile_fold_application_calculation(
                &term.operation,
                &fold.op,
                &[&accumulated, &term_value],
                position,
            )?;
            let argument_number = exact_rational_literal(&argument, "ℂ")?;
            let term_number = exact_rational_literal(&term_value, "ℂ")?;
            let seed_number = exact_rational_literal(&accumulated, "ℂ")?;
            let step_number = exact_rational_literal(&step_value, "ℂ")?;
            lines.push(format!("have _term_{i} : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number {argument_number}) = M.number {term_number} := {term_proof}"));
            lines.push(format!("have _step_{i} : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number {seed_number}) (M.number {term_number})) = M.number {step_number} := {step_proof}"));
            rewrites.extend([format!("_term_{i}"), format!("_step_{i}")]);
            indices.push(format!("({index} : ℤ)"));
            accumulated = step_value;
        }
        let other_number = self.compile_numeric_observation(other, position)?;
        if EvalRational::from_obj(&evidence.value).as_ref() != Some(&accumulated)
            || EvalRational::from_obj(&certificate.left_value).as_ref() != Some(&accumulated)
            || EvalRational::from_obj(&certificate.right_value).as_ref() != Some(&accumulated)
            || other_number.3.as_ref() != Some(&accumulated)
        {
            return Err(LeanCompileError::unsupported("FoldCalculation/ResultValue"));
        }
        let a = bounds.start_integer;
        let b = bounds.end_integer;
        let output = exact_rational_literal(&accumulated, "ℂ")?;
        lines.push(format!("apply Litex.rangeFoldDenote _fold ({a} : ℤ) ({b} : ℤ) ({}.trans (congrArg M.number (by norm_num))) ({}.trans (congrArg M.number (by norm_num))) (M.number {output})", first.1, last.1));
        lines.push(format!(
            "have _indices : Litex.integerFoldIndices ({a} : ℤ) ({b} : ℤ) = [{}] := by decide",
            indices.join(", ")
        ));
        lines.push(format!(
            "norm_num [Litex.foldValue, Litex.foldApply2, _indices, {}]",
            rewrites.join(", ")
        ));
        let denotation = format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "));
        let equal = format!("(Litex.NativeBridge.sameOfDenoteNumber {source} {} {output} {} {denotation} {} (by norm_num))", self.compile_object_reference(other, position)?, other_number.0, other_number.1);
        Ok(if reverse {
            format!("({equal}).symm")
        } else {
            equal
        })
    }

    fn compile_fold_application_calculation(
        &self,
        result: &FunctionApplicationEvaluationResult,
        function: &Obj,
        arguments: &[&EvalRational],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = &result.application else {
            return Err(LeanCompileError::unsupported("FoldCalculation/Application"));
        };
        let head = function_head_object(call.head.as_ref())?;
        if head.ir() != function.ir()
            || call.body.len() != 1
            || call.body[0].len() != arguments.len()
            || !(1..=2).contains(&arguments.len())
            || call.body[0]
                .iter()
                .zip(arguments)
                .any(|(a, b)| EvalRational::from_obj(a).as_ref() != Some(*b))
        {
            return Err(LeanCompileError::unsupported(
                "FoldCalculation/ApplicationArguments",
            ));
        }
        let FunctionApplicationExpansionProof::Anonymous(expansion) = &result.expansion else {
            return Err(LeanCompileError::unsupported(
                "FoldCalculation/ExpansionRoute",
            ));
        };
        let literal = expansion
            .function_equal
            .path
            .last()
            .map(|(_, to, _)| to)
            .unwrap_or(&head);
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous)) = literal else {
            return Err(LeanCompileError::unsupported(
                "FoldCalculation/FunctionBody",
            ));
        };
        let parameters = anonymous
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if parameters.len() != arguments.len()
            || !Self::function_uses_numeric_interface(&anonymous.body)
        {
            return Err(LeanCompileError::unsupported(
                "FoldCalculation/FunctionSignature",
            ));
        }
        let substitution = parameters
            .iter()
            .zip(&call.body[0])
            .map(|(p, a)| (p.id, a.as_ref().clone()))
            .collect::<HashMap<_, _>>();
        let value = EvalRational::from_obj(&result.value)
            .ok_or_else(|| LeanCompileError::unsupported("FoldCalculation/ApplicationValue"))?;
        if !instantiated_object_matches(
            &anonymous.equal_to,
            &expansion.expanded_body,
            &substitution,
        ) || !closed_scalar_body(&expansion.expanded_body)
            || EvalRational::from_obj(&expansion.expanded_body).as_ref() != Some(&value)
        {
            return Err(LeanCompileError::unsupported(
                "FoldCalculation/ExpandedValue",
            ));
        }
        ensure_object(&result.application, &result.application_well_defined)?;
        let cursor = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&result.application_well_defined),
            usize::MAX,
        );
        let call_term = self.compile_wd(&result.application_well_defined, &cursor)?;
        let literal_term = self.compile_object_reference(literal, &cursor)?;
        let equality =
            self.compile_equality_path(&head, literal, &expansion.function_equal, &cursor)?;
        let (signature_args, target) =
            self.compile_function_constructor_arguments(&anonymous.body, &cursor)?;
        let guard = self.compile_function_guard_template(&anonymous.body, &cursor)?;
        let raw = self.compile_normalization_value(&expansion.expanded_body, &cursor)?;
        let number = exact_rational_literal(&value, "ℂ")?;
        let mut observations = Vec::new();
        for (i, argument) in call.body[0].iter().enumerate() {
            let obs = self.compile_numeric_observation(argument, &cursor)?;
            let n = exact_rational_literal(arguments[i], "ℂ")?;
            let field = if arguments.len() == 1 {
                "argument"
            } else if i == 0 {
                "first"
            } else {
                "second"
            };
            observations.push(format!("have _argument_{i} : Litex.denote _call.val.{field} = M.number {n} := ({}).trans (congrArg M.number (by norm_num : {} = {n}))", obs.1, obs.0));
        }
        let template = self.compile_function_body_template(anonymous, &cursor)?;
        let numeric_laws = "Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers";
        let (input, domain, body, argument_equality) = if arguments.len() == 1 {
            (
                "(Litex.denote _call.val.argument)".to_string(),
                if target {
                    "oneTarget_domain"
                } else {
                    "one_domain"
                },
                format!("by change {template} (Litex.denote _call.val.argument) = {raw}; norm_num [_argument_0, {numeric_laws}]"),
                "_argument_0".to_string(),
            )
        } else {
            let body = self.compile_function_body_template(anonymous, &cursor)?;
            ("(Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))".to_string(), if target { "twoTarget_domain" } else { "two_domain" },
             format!("by change {body} (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = {raw}; norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, {numeric_laws}]"),
             "(congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)".to_string())
        };
        let domain_args = if arguments.len() == 1 { "_" } else { "_ _" };
        Ok(format!("(by\n  let _call := {call_term}\n  let _literal := {literal_term}\n  have _head : Litex.Same _call.val.function _literal := {equality}\n  have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f {input}) _head\n  have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd {input} ((Litex.FunctionSignature.{domain} {signature_args} {guard} {domain_args}).mpr _call.wd.2)\n  {}\n  have _body : _literal.val.bodyValue {input} = {raw} := {body}\n  have _calculated : {raw} = M.number {number} := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]\n  exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) {argument_equality}).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))", observations.join("\n  ")))
    }
}
