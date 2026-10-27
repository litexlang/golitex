use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_aggregate_value(
        &self,
        evaluation: &AggregateEvaluationResult,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String), LeanCompileError> {
        let (source, enumeration, terms, value, product) = match evaluation {
            AggregateEvaluationResult::SumOfFiniteSet(p) => {
                (&p.source, &p.enumeration, &p.terms, &p.value, false)
            }
            AggregateEvaluationResult::ProductOfFiniteSet(p) => {
                (&p.source, &p.enumeration, &p.terms, &p.value, true)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/CalculationBranch",
                ))
            }
        };
        let (set, function) = match source {
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(p)) if !product => {
                (&p.set, &p.func)
            }
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) if product => {
                (&p.set, &p.func)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/CalculationConstructor",
                ))
            }
        };
        let Obj::SetFormer(SetFormer::ListSet(list)) = &enumeration.resolved_set else {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/EnumerationShape",
            ));
        };
        if !enumeration.cited_equal_fact_ids.is_empty()
            || enumeration.elements.len() != list.list.len()
            || terms.len() != list.list.len()
        {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/EnumerationStages",
            ));
        }
        let source_term = self.compile_object_reference(source, position)?;
        let standard_input = position
            .with_visible_wd(source, &mut |wd, _| {
                let ObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::IteratedOperator(p),
                    ..
                } = wd
                else {
                    return Err(LeanCompileError::unsupported(
                        "FiniteAggregate/CalculationWD",
                    ));
                };
                Self::finite_aggregate_uses_standard_input(p)
            })?
            .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/CalculationProducer"))?;
        let denote_law = if standard_input {
            "finiteAggregateListDenote"
        } else {
            "finiteAggregateOnListDenote"
        };

        let enumerated_term = self.compile_object_reference(&enumeration.resolved_set, position)?;
        let same = self.compile_equality_path(
            set,
            &enumeration.resolved_set,
            &enumeration.set_equality,
            position,
        )?;
        let n = list.list.len();
        let mut lines = vec![
            format!("let _aggregate := {source_term}"),
            format!("let _enumerated := {enumerated_term}"),
            format!("have _enumeration_same : Litex.Same _aggregate.val.set _enumerated := {same}"),
            "let _collection_tail_0 := _enumerated".into(),
        ];
        for i in 0..n {
            lines.push(format!(
                "let _collection_tail_{} := _collection_tail_{i}.val.tail",
                i + 1
            ));
        }
        let mut observations = Vec::new();
        let mut numbers = Vec::new();
        let mut term_facts = Vec::new();
        let mut accumulated = EvalRational::new(if product { 1 } else { 0 }, 1).unwrap();
        for (i, ((raw, argument), term)) in list
            .list
            .iter()
            .zip(&enumeration.elements)
            .zip(terms)
            .enumerate()
        {
            let observation = self.compile_numeric_observation(raw, position)?;
            let argument_value = EvalRational::from_obj(argument)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/ArgumentValue"))?;
            if observation.3.as_ref() != Some(&argument_value)
                || argument != &term.argument
                || !term.nested_aggregate_evidence.is_empty()
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/TermEnumeration",
                ));
            }
            let term_value = EvalRational::from_obj(&term.value)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/TermValue"))?;
            accumulated = if product {
                accumulated.mul(&term_value)
            } else {
                accumulated.add(&term_value)
            }
            .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/Overflow"))?;
            if EvalRational::from_obj(&term.accumulated_value).as_ref() != Some(&accumulated) {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/Accumulation",
                ));
            }
            let argument_number = exact_rational_literal(&argument_value, "ℂ")?;
            let term_number = exact_rational_literal(&term_value, "ℂ")?;
            let beta = self.compile_aggregate_term(term, function, &term_value, position)?;
            let name = format!("_aggregate_term_{i}");
            lines.push(format!("have {name} : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue (Litex.denote _aggregate.val.function) (M.number {argument_number})) = {term_number} := (congrArg (Litex.NativeBridge.complexValue (M := M)) {beta}).trans (Litex.NativeBridge.complexValue_number {term_number})"));
            observations.push(observation);
            numbers.push(argument_number);
            term_facts.push(name);
        }
        if EvalRational::from_obj(value).as_ref() != Some(&accumulated) {
            return Err(LeanCompileError::unsupported("FiniteAggregate/ResultValue"));
        }
        lines.push(format!("have _members_{n} : ∀ x, M.mem x (Litex.denote _collection_tail_{n}) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty"));
        for i in (0..n).rev() {
            let obs = &observations[i];
            let number = &numbers[i];
            lines.push(format!("have _number_{i} : Litex.denote _collection_tail_{i}.val.element = M.number {number} := ({}).trans (congrArg M.number (by norm_num : {} = {number}))", obs.1, obs.0));
            let tail = numbers[i + 1..]
                .iter()
                .map(|n| format!("M.number {n}"))
                .collect::<Vec<_>>()
                .join(", ");
            lines.push(format!("have _members_{i} := Litex.finiteMembersInsert _collection_tail_{i} (M.number {number}) [{tail}] _number_{i} _members_{}", i+1));
        }
        let output = exact_rational_literal(&accumulated, "ℂ")?;
        lines.push(format!(
            "apply Litex.{denote_law} _aggregate [{}] {output}",
            numbers.join(", ")
        ));
        lines.push("· intro x\n  rw [_enumeration_same]\n  exact _members_0 x".into());
        let mut normalization = vec!["List.toFinset_cons".into(), "List.toFinset_nil".into()];
        normalization.extend(term_facts);
        lines.push(format!("· norm_num [{}]", normalization.join(", ")));
        let denotation = format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "));
        Ok((accumulated, denotation))
    }
}
