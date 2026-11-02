use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FiniteSetEnumerationResult,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_aggregate_value(
        &self,
        evaluation: &AggregateEvaluationResult,
        term_values: &[String],
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
        let (arguments, enumeration_proof) =
            self.compile_numeric_enumeration(set, enumeration, position)?;
        if terms.len() != arguments.len() || term_values.len() != terms.len() {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/EnumerationStages",
            ));
        }
        if terms.is_empty() {
            let value_expected = EvalRational::new(if product { 1 } else { 0 }, 1).unwrap();
            if EvalRational::from_obj(value).as_ref() != Some(&value_expected) {
                return Err(LeanCompileError::unsupported("FiniteAggregate/EmptyValue"));
            }
            let raw =
                self.compile_function_raw_expression_bound(source, position, &Default::default())?;
            let number = exact_rational_literal(&value_expected, "ℂ")?;
            return Ok((value_expected, format!("(show {raw} = M.number {number} from by\n  apply congrArg M.number\n  apply Litex.finiteAggregateValueEmpty\n  intro x hx\n  have impossible := ({enumeration_proof} x).mp hx\n  cases impossible)")));
        }
        let function_value = self.compile_normalization_value(function, position)?;
        let set_value = self.compile_normalization_value(set, position)?;
        let mut lines = vec![format!("let _aggregate_function := {function_value}")];
        let numbers = arguments
            .iter()
            .map(|n| exact_rational_literal(n, "ℂ"))
            .collect::<Result<Vec<_>, _>>()?;
        let mut term_facts = Vec::new();
        let mut accumulated = EvalRational::new(if product { 1 } else { 0 }, 1).unwrap();
        for (i, (argument_value, term)) in arguments.iter().zip(terms).enumerate() {
            if EvalRational::from_obj(&term.argument).as_ref() != Some(argument_value) {
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
            let beta = self.compile_aggregate_term(
                term,
                function,
                &term_value,
                &term_values[i],
                position,
            )?;
            let name = format!("_aggregate_term_{i}");
            lines.push(format!("have {name} : Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue _aggregate_function (M.number {argument_number})) = {term_number} := (congrArg (Litex.NativeBridge.complexValue (M := M)) {beta}).trans (Litex.NativeBridge.complexValue_number {term_number})"));
            term_facts.push(name);
        }
        if EvalRational::from_obj(value).as_ref() != Some(&accumulated) {
            return Err(LeanCompileError::unsupported("FiniteAggregate/ResultValue"));
        }
        let output = exact_rational_literal(&accumulated, "ℂ")?;
        lines.push("apply congrArg M.number".into());
        lines.push(format!(
            "apply Litex.finiteAggregateValueList {product} {set_value} (fun x => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue _aggregate_function x)) [{}] {output}",
            numbers.join(", ")
        ));
        lines.push(format!("· exact {enumeration_proof}"));
        let mut normalization = vec!["List.toFinset_cons".into(), "List.toFinset_nil".into()];
        normalization.extend(term_facts);
        lines.push(format!("· norm_num [{}]", normalization.join(", ")));
        let denotation = format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "));
        Ok((accumulated, denotation))
    }
    /// Replay the original numeric enumeration and its exact set-equality path.
    pub(in crate::compile_to_lean) fn compile_numeric_enumeration(
        &self,
        set: &Obj,
        enumeration: &FiniteSetEnumerationResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<EvalRational>, String), LeanCompileError> {
        if let Obj::SetFormer(SetFormer::ClosedRange(range)) = &enumeration.resolved_set {
            if set.ir() != enumeration.resolved_set.ir()
                || !enumeration.set_equality.path.is_empty()
                || !enumeration.cited_equal_fact_ids.is_empty()
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/ClosedRangeEnumeration",
                ));
            }
            let a = closed_integer(&range.start)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/ClosedRangeLower"))?;
            let b = closed_integer(&range.end)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/ClosedRangeUpper"))?;
            let (_, lower) = self.compile_eval_closed_value(&range.start, position)?;
            let (_, upper) = self.compile_eval_closed_value(&range.end, position)?;
            let raw = self.compile_normalization_value(set, position)?;
            if a <= b {
                let count = b
                    .checked_sub(a)
                    .and_then(|n| n.checked_add(1))
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("FiniteAggregate/ClosedRangeSize")
                    })?;
                if enumeration.elements.len() != count {
                    return Err(LeanCompileError::unsupported(
                        "FiniteAggregate/ClosedRangeSize",
                    ));
                }
                let mut values = Vec::with_capacity(count);
                let mut indices = Vec::with_capacity(count);
                let mut numbers = Vec::with_capacity(count);
                for (index, element) in enumeration.elements.iter().enumerate() {
                    let expected = a.checked_add(index as i128).ok_or_else(|| {
                        LeanCompileError::unsupported("FiniteAggregate/ClosedRangeSize")
                    })?;
                    let value = EvalRational::from_obj(element)
                        .filter(|v| v.to_i128_if_integer() == Some(expected))
                        .ok_or_else(|| {
                            LeanCompileError::unsupported("FiniteAggregate/ClosedRangeElement")
                        })?;
                    values.push(value);
                    indices.push(format!("({expected} : ℤ)"));
                    numbers.push(format!("M.number ({expected} : ℂ)"));
                }
                let integer_list = indices.join(", ");
                return Ok((values, format!("(show ∀ x, M.mem x {raw} ↔ x ∈ ([{}] : List M.Value) from by\n  intro x\n  have bounds : {raw} = Litex.closedRangeValue (M.number ({a} : ℂ)) (M.number ({b} : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) {lower} {upper}\n  rw [bounds]\n  simpa only [List.map_cons, List.map_nil, Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using (Litex.closedRangeValueListMembers (M := M) ({a} : ℤ) ({b} : ℤ) [{integer_list}] (by decide) x))", numbers.join(", "))));
            }
            if !enumeration.elements.is_empty() {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/ClosedRangeSize",
                ));
            }
            return Ok((vec![], format!("(show ∀ x, M.mem x {raw} ↔ x ∈ ([] : List M.Value) from by\n  intro x\n  have bounds : {raw} = Litex.closedRangeValue (M.number ({a} : ℂ)) (M.number ({b} : ℂ)) := congrArg₂ (Litex.closedRangeValue (M := M)) {lower} {upper}\n  have members := Litex.closedRangeValue_members (M := M) ({a} : ℤ) ({b} : ℤ) x\n  norm_num at members\n  rw [bounds, members]\n  constructor\n  · rintro ⟨k, _, hlo, hhi⟩\n    omega\n  · intro h\n    cases h)")));
        }
        let Obj::SetFormer(SetFormer::ListSet(list)) = &enumeration.resolved_set else {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/EnumerationShape",
            ));
        };
        if !enumeration.cited_equal_fact_ids.is_empty()
            || list.list.len() != enumeration.elements.len()
        {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/EnumerationStages",
            ));
        }
        let set_term = self.compile_object_reference(set, position)?;
        let enumerated = self.compile_object_reference(&enumeration.resolved_set, position)?;
        let same = self.compile_equality_path(
            set,
            &enumeration.resolved_set,
            &enumeration.set_equality,
            position,
        )?;
        let mut lines = vec![
            format!("let _enumerated := {enumerated}"),
            format!("have _enumeration_same : Litex.Same {set_term} _enumerated := {same}"),
            "let _collection_tail_0 := _enumerated".into(),
        ];
        let mut values = Vec::new();
        let mut observations = Vec::new();
        let mut numbers = Vec::new();
        for (i, (raw, argument)) in list.list.iter().zip(&enumeration.elements).enumerate() {
            let observation = self.compile_numeric_observation(raw, position)?;
            let value = EvalRational::from_obj(argument)
                .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/ArgumentValue"))?;
            if observation.3.as_ref() != Some(&value) || values.contains(&value) {
                return Err(LeanCompileError::unsupported(
                    "FiniteAggregate/TermEnumeration",
                ));
            }
            numbers.push(exact_rational_literal(&value, "ℂ")?);
            values.push(value);
            observations.push(observation);
            lines.push(format!(
                "let _collection_tail_{} := _collection_tail_{i}.val.tail",
                i + 1
            ));
        }
        let n = values.len();
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
        let members = numbers
            .iter()
            .map(|n| format!("M.number {n}"))
            .collect::<Vec<_>>()
            .join(", ");
        lines.push(format!("intro x\nexact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([{members}] : List M.Value)) _enumeration_same) (_members_0 x)"));
        Ok((
            values,
            format!(
                "(show ∀ x, M.mem x (Litex.denote {set_term}) ↔ x ∈ ([{members}] : List M.Value) from by\n  {})",
                lines.join("\n").replace('\n', "\n  ")
            ),
        ))
    }
}
