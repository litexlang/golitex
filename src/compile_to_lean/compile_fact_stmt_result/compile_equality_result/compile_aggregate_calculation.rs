use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{AggregateEvaluationResult, AggregateTermEvaluationResult, AggregateTermExpansion};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_by_aggregate_calculation::AggregateCalculationBuiltinRuleProof;
use crate::prelude::*;
use super::compile_function_definition::function_head_object;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_aggregate_calculation(
        &self,
        fact: &EqualFact,
        proof: &AggregateCalculationBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.rewritten_left != fact.left
            || proof.rewritten_right != fact.right
            || !proof.cited_equal_fact_ids.is_empty()
            || !proof.matrix_scalar_evaluations.is_empty()
            || !proof.function_evaluations.is_empty()
            || !proof.algo_evaluations.is_empty()
        {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/AdditionalStages",
            ));
        }
        // The evaluator visits left then right, recording completed aggregates.
        // Consume that original postorder backwards, as for command evaluation.
        let mut remaining = proof.aggregate_evaluations.len();
        let (right_value, right, right_cites) = self.compile_eval_value(
            &proof.rewritten_right,
            &[],
            &mut 0,
            &proof.aggregate_evaluations,
            &mut remaining,
            position,
        )?;
        let (left_value, left, left_cites) = self.compile_eval_value(
            &proof.rewritten_left,
            &[],
            &mut 0,
            &proof.aggregate_evaluations,
            &mut remaining,
            position,
        )?;
        if remaining != 0
            || !left_cites.is_empty()
            || !right_cites.is_empty()
            || left_value != right_value
            || EvalRational::from_obj(&proof.left_value).as_ref() != Some(&left_value)
            || EvalRational::from_obj(&proof.right_value).as_ref() != Some(&right_value)
        {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/ResultValue",
            ));
        }
        let left = self.compile_calculation_endpoint(&fact.left, &left_value, left, position)?;
        let right =
            self.compile_calculation_endpoint(&fact.right, &right_value, right, position)?;
        Ok(format!(
            "(show Litex.Same {} {} from ({left}).trans ({right}).symm)",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?
        ))
    }

    // A closed scalar endpoint can use a previously registered numeric WD
    // representation (for example a stored -6 rather than a fresh neg(6)).
    // Observe that original representation and check the same exact result.
    pub(in crate::compile_to_lean) fn compile_calculation_endpoint(
        &self,
        object: &Obj,
        value: &EvalRational,
        raw_proof: String,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if crate::rational_expression::ClosedNumericExpr::try_from_obj(object).is_none() {
            // Cached numeric children may use a signed numeral where the
            // source AST uses unary negation. Their denotations agree by the
            // numeric embedding law, including below function applications.
            let term = self.compile_object_reference(object, position)?;
            let output = exact_rational_literal(value, "ℂ")?;
            return Ok(format!("(show Litex.denote {term} = M.number {output} from by simpa only [M.neg_numbers] using {raw_proof})"));
        }
        let observation = self.compile_numeric_observation(object, position)?;
        if observation.3.as_ref() != Some(value) {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/EndpointValue",
            ));
        }
        let output = exact_rational_literal(value, "ℂ")?;
        Ok(format!(
            "({}).trans (congrArg M.number (by norm_num : {} = {output}))",
            observation.1, observation.0
        ))
    }

    pub(in crate::compile_to_lean) fn compile_range_aggregate_value(
        &self,
        evaluation: &AggregateEvaluationResult,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String), LeanCompileError> {
        let (source, bounds, terms, value, product) = match evaluation {
            AggregateEvaluationResult::Sum(p) => (&p.source, &p.bounds, &p.terms, &p.value, false),
            AggregateEvaluationResult::Product(p) => {
                (&p.source, &p.bounds, &p.terms, &p.value, true)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "AggregateCalculation/FiniteSetOrFold",
                ))
            }
        };
        let (first, last, function) = match source {
            Obj::IteratedOperator(IteratedOperator::Sum(p)) if !product => {
                (&p.start, &p.end, &p.func)
            }
            Obj::IteratedOperator(IteratedOperator::Product(p)) if product => {
                (&p.start, &p.end, &p.func)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "AggregateCalculation/Constructor",
                ))
            }
        };
        if bounds.start.ir() != first.ir()
            || bounds.end.ir() != last.ir()
            || !bounds.cited_equal_fact_ids.is_empty()
        {
            return Err(LeanCompileError::unsupported("AggregateCalculation/Bounds"));
        }
        let first_number = self.compile_numeric_observation(first, position)?;
        let last_number = self.compile_numeric_observation(last, position)?;
        if first_number.3.as_ref().and_then(|n| n.to_i128_if_integer())
            != Some(bounds.start_integer)
            || last_number.3.as_ref().and_then(|n| n.to_i128_if_integer())
                != Some(bounds.end_integer)
            || bounds
                .end_integer
                .checked_sub(bounds.start_integer)
                .and_then(|n| n.checked_add(1))
                .and_then(|n| usize::try_from(n).ok())
                != Some(terms.len())
            || terms.is_empty()
        {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/IndexEnumeration",
            ));
        }
        let mut accumulated = EvalRational::new(if product { 1 } else { 0 }, 1).unwrap();
        let mut lines = vec![format!(
            "let _aggregate := {}",
            self.compile_object_reference(source, position)?
        )];
        let mut indices = Vec::new();
        let mut facts = Vec::new();
        for (i, term) in terms.iter().enumerate() {
            let index = bounds.start_integer.checked_add(i as i128).ok_or_else(|| {
                LeanCompileError::unsupported("AggregateCalculation/IndexOverflow")
            })?;
            if EvalRational::from_obj(&term.argument).and_then(|n| n.to_i128_if_integer())
                != Some(index)
                || !term.nested_aggregate_evidence.is_empty()
            {
                return Err(LeanCompileError::unsupported(
                    "AggregateCalculation/TermIndex",
                ));
            }
            let term_value = EvalRational::from_obj(&term.value)
                .ok_or_else(|| LeanCompileError::unsupported("AggregateCalculation/TermValue"))?;
            accumulated = if product {
                accumulated.mul(&term_value)
            } else {
                accumulated.add(&term_value)
            }
            .ok_or_else(|| LeanCompileError::unsupported("AggregateCalculation/Overflow"))?;
            if EvalRational::from_obj(&term.accumulated_value).as_ref() != Some(&accumulated) {
                return Err(LeanCompileError::unsupported(
                    "AggregateCalculation/Accumulation",
                ));
            }
            let beta = self.compile_aggregate_term(term, function, &term_value, position)?;
            let number = exact_rational_literal(&term_value, "ℂ")?;
            let name = format!("_aggregate_term_{i}");
            lines.push(format!("have {name} : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number ({index} : ℂ))) = {number} := (congrArg (Litex.NativeBridge.complexValue (M := M)) {beta}).trans (Litex.NativeBridge.complexValue_number {number})"));
            indices.push(format!("({index} : ℤ)"));
            facts.push(name);
        }
        if EvalRational::from_obj(value).as_ref() != Some(&accumulated) {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/ResultValue",
            ));
        }
        let a = bounds.start_integer;
        let b = bounds.end_integer;
        let output = exact_rational_literal(&accumulated, "ℂ")?;
        lines.push(format!("apply Litex.rangeAggregateDenote _aggregate ({a} : ℤ) ({b} : ℤ) ({}.trans (congrArg M.number (by norm_num))) ({}.trans (congrArg M.number (by norm_num))) {output}", first_number.1, last_number.1));
        lines.push(format!(
            "have _indices : Finset.Icc ({a} : ℤ) ({b} : ℤ) = {{{}}} := by decide",
            indices.join(", ")
        ));
        lines.push(format!(
            "norm_num [Litex.nativeRangeAggregate, _indices, {}]",
            facts.join(", ")
        ));
        let denotation = format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "));
        Ok((accumulated, denotation))
    }

    pub(super) fn compile_aggregate_term(
        &self,
        term: &AggregateTermEvaluationResult,
        function: &Obj,
        value: &EvalRational,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AggregateTermExpansion::Function(expansion) = &term.expansion else {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/Algorithm",
            ));
        };
        let Obj::FnObj(call) = &term.application else {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/Application",
            ));
        };
        let head = function_head_object(call.head.as_ref())?;
        if head.ir() != function.ir()
            || call.body.len() != 1
            || call.body[0].len() != 1
            || call.body[0][0].as_ref() != &term.argument
        {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/ApplicationSubject",
            ));
        }
        let literal = expansion
            .function_equal
            .path
            .last()
            .map(|(_, to, _)| to)
            .unwrap_or(&head);
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous)) = literal else {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/FunctionBody",
            ));
        };
        let params = anonymous
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if params.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/FunctionSignature",
            ));
        }
        let substitution = HashMap::from([(params[0].id, term.argument.clone())]);
        if !instantiated_object_matches(
            &anonymous.equal_to,
            &expansion.expanded_body,
            &substitution,
        ) || !closed_scalar_body(&expansion.expanded_body)
            || EvalRational::from_obj(&expansion.expanded_body).as_ref() != Some(value)
        {
            return Err(LeanCompileError::unsupported(
                "AggregateCalculation/ExpandedValue",
            ));
        }
        ensure_object(&term.application, &term.application_well_defined)?;
        let cursor = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&term.application_well_defined),
            usize::MAX,
        );
        let call_term = self.compile_wd(&term.application_well_defined, &cursor)?;
        let equality =
            self.compile_equality_path(&head, literal, &expansion.function_equal, &cursor)?;
        let literal_term = self.compile_object_reference(literal, &cursor)?;
        let domain_proof = if Self::function_uses_numeric_interface(&anonymous.body) {
            let (args, target) =
                self.compile_function_constructor_arguments(&anonymous.body, &cursor)?;
            let guard = self.compile_function_guard_template(&anonymous.body, &cursor)?;
            let domain = if target {
                "oneTarget_domain"
            } else {
                "one_domain"
            };
            format!("((Litex.FunctionSignature.{domain} {args} {guard} _).mpr _call.wd.2)")
        } else {
            "_call.wd.2".to_string()
        };
        let raw = self.compile_normalization_value(&expansion.expanded_body, &cursor)?;
        let number = exact_rational_literal(value, "ℂ")?;
        let argument = self.compile_numeric_observation(&term.argument, &cursor)?;
        let argument_value = EvalRational::from_obj(&term.argument)
            .ok_or_else(|| LeanCompileError::unsupported("AggregateCalculation/ArgumentValue"))?;
        let argument_number = exact_rational_literal(&argument_value, "ℂ")?;
        let argument_denote = argument.1;
        let argument_expr = argument.0;
        Ok(format!("(by\n  let _call := {call_term}\n  let _literal := {literal_term}\n  have _head : Litex.Same _call.val.function _literal := {equality}\n  have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head\n  have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) {domain_proof}\n  have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = {raw} := rfl\n  have _calculated : {raw} = M.number {number} := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]\n  have _argument : Litex.denote _call.val.argument = M.number {argument_number} := ({argument_denote}).trans (congrArg M.number (by norm_num : {argument_expr} = {argument_number}))\n  exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))"))
    }
}

pub(super) fn closed_scalar_body(object: &Obj) -> bool {
    match object {
        Obj::Literal(Literal::Number(_)) => true,
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
            closed_scalar_body(&p.left) && closed_scalar_body(&p.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            closed_scalar_body(&p.left) && closed_scalar_body(&p.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
            closed_scalar_body(&p.left) && closed_scalar_body(&p.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
            closed_scalar_body(&p.left)
                && closed_scalar_body(&p.right)
                && EvalRational::from_obj(&p.right).is_some_and(|v| !v.is_zero())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => closed_scalar_body(&p.arg),
        _ => false,
    }
}
