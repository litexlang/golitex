//! Replay the recorded reduction tape; structural congruence adds no search.
use super::helper::{
    ensure_object, exact_rational_literal, finite_vector_equality, instantiated_object_matches,
};
use super::source_position::{visit_complete_wd, SourceConstructor, SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;
use crate::execute::execute_fact_stmt::multivariable::expression::{
    call_head, literal_dimension, MultivariableReductionProof, MultivariableReductionStep as Step,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashMap;

/// A single original body being applied at its recorded arguments. This is a
/// borrowed recursive input, not a compiler registry or a new WD result.
struct AppliedBody<'a> {
    wd: &'a ObjWellDefinedProof,
    substitution: HashMap<IdentifierId, Obj>,
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableReduction/{stage}"))
}

/// Resolve the recorded call constructor under its enclosing beta substitution.
/// Both ordinary and grouped beta must use this same original WD, not WD for a
/// newly instantiated object. The callback keeps its original citation scope.
fn with_original_call<T>(
    source: &Obj,
    position: &SourcePosition<'_>,
    applied: Option<&AppliedBody<'_>>,
    emit: &mut impl FnMut(&ObjWellDefinedProof, &SourcePosition<'_>) -> Result<T, LeanCompileError>,
) -> Result<Option<T>, LeanCompileError> {
    let Some(body) = applied else {
        return position.with_visible_wd(source, emit);
    };
    visit_complete_wd(
        body.wd,
        position,
        &mut |constructor, site| {
            let SourceConstructor::Checked(wd) = constructor else {
                return Ok(None);
            };
            if !matches!(
                wd.detailed_ref(),
                DetailedObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(_),
                    ..
                }
            ) || !instantiated_object_matches(wd.obj(), source, &body.substitution)
            {
                return Ok(None);
            }
            emit(wd, site).map(Some)
        },
        &mut |_, _| Ok(None),
    )
}

impl LitexToLeanCompiler {
    pub(super) fn compile_multivariable_reduction(
        &self,
        proof: &MultivariableReductionProof,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let mut cursor = 0;
        let (result, term) = self.compile_multivariable_reduction_node(
            &proof.source,
            &proof.steps,
            &mut cursor,
            position,
            bindings,
            None,
            0,
        )?;
        if cursor != proof.steps.len() || result != proof.result {
            return Err(invalid("TapeEndpoint"));
        }
        Ok(term)
    }

    /// Close WD-consuming reductions under the literal's original parameter
    /// stores, then instantiate that proved equality on a coordinate path.
    pub(super) fn compile_multivariable_literal_reduction(
        &self,
        function: &AnonymousFn,
        proof: &MultivariableReductionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.source != *function.equal_to {
            return Err(invalid("BodySource"));
        }
        let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
        position.with_visible_wd(&literal, &mut |original, producer| {
            let DetailedObjWellDefinedProof::ByDef { obj, proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd))
            } = original.detailed_ref() else {return Err(invalid("BodyWD"));};
            if obj != &literal || Self::function_uses_numeric_interface(&function.body) {
                return Err(invalid("BodySignature"));
            }
            let signature = &function.body;
            let parameters = signature.set_bound_parameters.groups.iter()
                .flat_map(|group| &group.params).collect::<Vec<_>>();
            let [parameter] = parameters.as_slice() else {return Err(invalid("BodyArity"));};
            let scope = SourcePosition::new(Some(producer), SourceOwner::WD(original), 0);
            let head = self.compile_function_binder_head(signature, &wd.param_type_well_defined,
                &wd.defined_params, &wd.assumed_dom_facts, &scope)?;
            let body_position = SourcePosition { before: self.function_header_stages(signature) + 1, ..scope };
            ensure_object(&proof.source, &wd.body_well_defined)?;
            let constructor = self.compile_wd(&wd.body_well_defined, &body_position)?;
            let complete = SourcePosition {before: body_position.before + 1, ..scope};
            let local = SourcePosition::new(Some(&complete), SourceOwner::ObjectLocal(&wd.body_well_defined), 0);
            let term = self.compile_multivariable_reduction(proof, &local, &HashMap::new())?;
            let bindings = HashMap::from([(parameter.id, "_beta_input".to_string())]);
            let left = self.compile_function_raw_expression_bound(&proof.source, &local, &bindings)?;
            let right = self.compile_function_raw_expression_bound(&proof.result, &local, &bindings)?;
            let inputs = self.compile_function_input_sets(signature, &scope)?;
            let output = self.compile_object_reference(&signature.ret_set, &body_position)?;
            let guard = self.compile_function_guard_template(signature, &scope)?;
            let (domain, sethood) = self.compile_function_base_domain(signature, &scope)?;
            let packed_guard = self.compile_function_packed_guard_template(signature, &scope)?;
            let fn_signature = self.compile_fn_signature(signature, &scope)?;
            Ok(format!("(show ∀ (_beta_input : M.Value), M.mem _beta_input ({fn_signature}).domain → {left}={right} from by\n  have _beta_checked : ∀ (_beta_input : M.Value), M.mem _beta_input (Litex.denote {}) → ({guard} _beta_input) → {left}={right} := by\n    {}\n    let {} := {}\n    exact {}\n  intro _beta_input _beta_domain\n  obtain ⟨_beta_member, _beta_guard⟩ := (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {output}) {sethood} (Litex.isSet {output}) {packed_guard} _beta_input).mp _beta_domain\n  exact _beta_checked _beta_input _beta_member _beta_guard)",
                inputs[0], head.replace('\n', "\n    "), local.object_local_name(),
                constructor.replace('\n', "\n    "), term.replace('\n', "\n    ")))
        })?.ok_or_else(|| invalid("BodyWD"))
    }

    /// Apply the original body proof under its own parameters. Equalities from
    /// the recorded argument reductions transport those parameters; local WD
    /// stays inside this proof and is never published to the caller's scope.
    fn compile_applied_body_reduction(
        &self,
        call_wd: &ObjWellDefinedProof,
        expanded: &Obj,
        arguments: &[Box<Obj>],
        equalities: &[String],
        steps: &[Step],
        cursor: &mut usize,
        caller: &SourcePosition<'_>,
        outer: Option<&AppliedBody<'_>>,
        depth: usize,
    ) -> Result<(Obj, String), LeanCompileError> {
        let DetailedObjWellDefinedProof::ByDef {
            obj: Obj::FnObj(call),
            proof: ObjWellDefinedProofByDef::FnObj(formation),
        } = call_wd.detailed_ref()
        else {
            return Err(invalid("AppliedCallWD"));
        };
        let head_object = call_head(&call.head);
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = &head_object else {
            return Err(invalid("AppliedLiteral"));
        };
        caller.with_visible_wd(&head_object, &mut |original, producer| {
            let DetailedObjWellDefinedProof::ByDef {proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd)), ..
            } = original.detailed_ref() else {return Err(invalid("AppliedBodyWD"));};
            ensure_object(&head_object, original)?;
            let signature = &function.body;
            let parameters = signature.set_bound_parameters.groups.iter()
                .flat_map(|group| &group.params).collect::<Vec<_>>();
            if parameters.len() != arguments.len() || equalities.len() != arguments.len()
                || call.body.len() != 1 || formation.child_obj_well_defined.len() != arguments.len() + 1
                || formation.requirement_fact_verified.len() != arguments.len() + signature.dom_facts.len() {
                return Err(invalid("AppliedArity"));
            }
            let mut substitution = outer.map_or_else(HashMap::new, |p| p.substitution.clone());
            for (parameter, argument) in parameters.iter().zip(arguments) {
                if substitution.insert(parameter.id, argument.as_ref().clone()).is_some() {
                    return Err(invalid("AppliedBinderIdentity"));
                }
            }
            if !instantiated_object_matches(&function.equal_to, expanded, &substitution) {
                return Err(invalid("AppliedBodyEndpoint"));
            }
            let scope = SourcePosition::new(Some(producer), SourceOwner::WD(original), 0);
            let head = self.compile_function_binder_head(signature, &wd.param_type_well_defined,
                &wd.defined_params, &wd.assumed_dom_facts, &scope)?;
            let body_position = SourcePosition {before: self.function_header_stages(signature) + 1, ..scope};
            ensure_object(&function.equal_to, &wd.body_well_defined)?;
            let constructor = self.compile_wd(&wd.body_well_defined, &body_position)?;
            let complete = SourcePosition {before: body_position.before + 1, ..scope};
            let local = SourcePosition::new(Some(&complete), SourceOwner::ObjectLocal(&wd.body_well_defined), 0);
            let applied = AppliedBody {wd: &wd.body_well_defined, substitution};
            let (result, tail) = self.compile_multivariable_reduction_node(
                expanded, steps, cursor, &local, &HashMap::new(), Some(&applied), depth,
            )?;
            let left = self.compile_normalization_value(expanded, &local)?;
            let right = self.compile_normalization_value(&result, &local)?;
            let equations = parameters.iter().zip(arguments).map(|(parameter, argument)| {
                Ok(format!("_raw_i{} = {}", parameter.id.value(), self.compile_normalization_value(argument, caller)?))
            }).collect::<Result<Vec<_>, LeanCompileError>>()?;
            let conclusion = format!("{} → {left} = {right}", equations.join(" → "));
            let quantified = self.compile_function_raw_quantified(signature, &conclusion, &scope)?;
            let eq_names = parameters.iter().map(|p| format!("_beta_eq_i{}", p.id.value())).collect::<Vec<_>>();
            let substitutions = parameters.iter().map(|p| format!("subst _raw_i{}", p.id.value())).collect::<Vec<_>>().join("\n");
            // Replay each requirement in its original call order. No membership
            // search is performed for the substituted/reduced argument values.
            // The preceding beta elimination already compiled this call WD.
            let call_position = SourcePosition::new(Some(caller), SourceOwner::WD(call_wd), 0);
            let terms = call.body[0].iter().map(|a| self.compile_object_reference(a, caller))
                .collect::<Result<Vec<_>, _>>()?;
            let requirements = formation.requirement_fact_verified.iter().enumerate().map(|(i, proof)| {
                self.compile_verify(proof, &SourcePosition {before: formation.child_obj_well_defined.len() + i, ..call_position}).map(|p| p.1)
            }).collect::<Result<Vec<_>, _>>()?;
            let (members, guard) = self.compile_function_domain_certificates(signature, &terms, &requirements, caller)?;
            let values = terms.iter().map(|term| format!("(Litex.denote {term})")).collect::<Vec<_>>();
            let transports = call.body[0].iter().zip(equalities).map(|(argument, equality)| {
                Ok(format!("(({}).trans {equality})", self.compile_normalization_denotation(argument, caller)?))
            }).collect::<Result<Vec<_>, LeanCompileError>>()?;
            Ok((result, format!("(by\n  have _beta_body : {quantified} := by\n    {}\n    intro {}\n    {}\n    let {} := {}\n    exact {}\n  exact _beta_body {} {} {guard} {})",
                head.replace('\n', "\n    "), eq_names.join(" "), substitutions.replace('\n', "\n    "),
                local.object_local_name(), constructor.replace('\n', "\n    "), tail.replace('\n', "\n    "),
                values.join(" "), members.join(" "), transports.join(" "))))
        })?.ok_or_else(|| invalid("AppliedOriginalLiteral"))
    }

    /// Borrow every typed receiver from the original complete call. A returned
    /// graph is eliminated using that receiver's membership, not a newly
    /// invented WD record for the substituted anonymous literal.
    fn compile_grouped_anonymous_reduction(
        &self,
        source: &Obj,
        wd: &ObjWellDefinedProof,
        steps: &[Step],
        cursor: &mut usize,
        first_arguments: &[Box<Obj>],
        first_equalities: &[String],
        producer: &SourcePosition<'_>,
        applied: Option<&AppliedBody<'_>>,
        depth: usize,
    ) -> Result<(Obj, String), LeanCompileError> {
        if let Some(body) = applied {
            if !instantiated_object_matches(wd.obj(), source, &body.substitution) {
                return Err(invalid("GroupedOriginalCall"));
            }
        } else {
            ensure_object(source, wd)?;
        }
        let Obj::FnObj(call) = source else {
            return Err(invalid("GroupedCall"));
        };
        let Obj::FnObj(original_call) = wd.obj() else {
            return Err(invalid("GroupedOriginalCall"));
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(evidence),
            ..
        } = wd.detailed_ref()
        else {
            return Err(invalid("GroupedCallWD"));
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(first)) = call_head(&call.head) else {
            return Err(invalid("GroupedHead"));
        };
        let fn_set = match &evidence.domain_fn_set {
            Some(
                FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }
                | FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                | FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. },
            ) => fn_set,
            _ => return Err(invalid("GroupedDomain")),
        };
        if !function_domains_alpha_equal(fn_set, &first.body) {
            return Err(invalid("GroupedDomain"));
        }
        let actual = self.compile_wd(wd, producer)?;
        let complete = SourcePosition::new(Some(producer), SourceOwner::WD(wd), usize::MAX);
        let local = SourcePosition::new(Some(&complete), SourceOwner::ObjectLocal(wd), 0);
        let original = local.object_local_name();
        let mut lines = vec![format!("let {original} := {actual}")];
        let mut current = Obj::FunctionSpace(FunctionSpace::AnonymousFn(first));
        let mut head_equal = "rfl".to_string();
        for (index, group) in call.body.iter().enumerate() {
            let (arguments, equalities) = if index == 0 {
                (first_arguments.to_vec(), first_equalities.to_vec())
            } else {
                let mut arguments = Vec::new();
                let mut equalities = Vec::new();
                for argument in group {
                    let (value, equality) = self.compile_multivariable_reduction_node(
                        argument,
                        steps,
                        cursor,
                        &local,
                        &HashMap::new(),
                        applied,
                        depth + 1,
                    )?;
                    arguments.push(Box::new(value));
                    equalities.push(equality);
                }
                (arguments, equalities)
            };
            let Some(Step::AnonymousBeta {
                function,
                arguments: recorded,
                expanded,
            }) = steps.get(*cursor)
            else {
                return Err(invalid("GroupedBetaStep"));
            };
            if current != Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()))
                || !function.body.dom_facts.is_empty()
                || recorded.len() != arguments.len()
                || recorded
                    .iter()
                    .zip(&arguments)
                    .any(|(a, b)| a != b.as_ref())
            {
                return Err(invalid("GroupedBetaArguments"));
            }
            let parameters = function
                .body
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .collect::<Vec<_>>();
            if parameters.len() != arguments.len() || arguments.is_empty() {
                return Err(invalid("GroupedArity"));
            }
            let mut substitution = HashMap::new();
            for (parameter, argument) in parameters.iter().zip(&arguments) {
                if substitution
                    .insert(parameter.id, argument.as_ref().clone())
                    .is_some()
                {
                    return Err(invalid("GroupedBinderIdentity"));
                }
            }
            if !instantiated_object_matches(&function.equal_to, expanded, &substitution) {
                return Err(invalid("GroupedBetaEndpoint"));
            }
            let (domain, output, body) =
                self.compile_function_literal_parts(function, &local, &HashMap::new())?;
            let graph =
                format!("(Litex.FunctionSemantics.graphValue (M := M) {domain} {output} {body})");
            let values = arguments
                .iter()
                .map(|a| self.compile_normalization_value(a, &local))
                .collect::<Result<Vec<_>, _>>()?;
            let input = if values.len() == 1 {
                values[0].clone()
            } else {
                format!(
                    "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                    values.join(", ")
                )
            };
            let reduction = if equalities.len() == 1 {
                equalities[0].clone()
            } else {
                format!(
                    "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) {})",
                    finite_vector_equality(&equalities)
                )
            };
            // This is the original stage's argument constructor. The current
            // group's raw value is related by the enclosing binder equations;
            // it must not demand WD for an instantiated nested argument.
            let original_group = original_call
                .body
                .get(index)
                .ok_or_else(|| invalid("GroupedOriginalArguments"))?;
            let packed =
                self.compile_normalization_packed_argument_denotation(original_group, &local)?;
            let input_equal = format!("(({packed}).trans {reduction})");
            let mut stage = original.clone();
            for _ in index + 1..call.body.len() {
                stage = format!("({stage}).val.function");
            }
            let raw = match expanded {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(next)) => {
                    self.compile_function_literal_value(next, &local, &HashMap::new())?
                }
                _ => self.compile_normalization_value(expanded, &local)?,
            };
            let template = self.compile_function_body_template(function, &local)?;
            let unpack = self.compile_function_packed_application_equality(&template, &values)?;
            lines.push(format!("have _grouped_head_{index} : Litex.denote ({stage}).val.function = {graph} := {head_equal}"));
            lines.push(format!("have _grouped_input_{index} : Litex.denote ({stage}).val.argument = {input} := {input_equal}"));
            lines.push(format!(
                "let _grouped_signature_{index} := ({stage}).val.signature"
            ));
            lines.push(format!("have _grouped_member_{index} : M.mem {graph} (Litex.FunctionSemantics.fnSetValue _grouped_signature_{index}.domain _grouped_signature_{index}.output) := (congrArg (fun _head => M.mem _head (Litex.FunctionSemantics.fnSetValue _grouped_signature_{index}.domain _grouped_signature_{index}.output)) _grouped_head_{index}).mp ({stage}).wd.1"));
            lines.push(format!("have _grouped_domain_{index} : M.mem {input} _grouped_signature_{index}.domain := (congrArg (fun _input => M.mem _input _grouped_signature_{index}.domain) _grouped_input_{index}).mp ({stage}).wd.2"));
            lines.push(format!("have _grouped_eq_{index} : Litex.denote {stage} = {raw} := (show Litex.denote {stage} = Litex.FunctionSemantics.callValue {graph} {input} from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) _grouped_head_{index} _grouped_input_{index}).trans ((Litex.FunctionSemantics.call_graphValue_of_fnSet {domain} {output} {body} _grouped_signature_{index}.domain _grouped_signature_{index}.output {input} _grouped_member_{index} _grouped_domain_{index}).trans (show {body} {input} = {raw} from {unpack}))"));
            *cursor += 1;
            if index + 1 == call.body.len() {
                let (result, tail) = self.compile_multivariable_reduction_node(
                    expanded,
                    steps,
                    cursor,
                    &local,
                    &HashMap::new(),
                    applied,
                    depth + 1,
                )?;
                let input = self.compile_normalization_value(source, &local)?;
                let output = self.compile_normalization_value(&result, &local)?;
                lines.push(format!("exact (show {input} = Litex.denote {original} from rfl).trans (_grouped_eq_{index}.trans {tail})"));
                return Ok((
                    result,
                    format!(
                        "(show {input} = {output} from by\n  {})",
                        lines.join("\n").replace('\n', "\n  ")
                    ),
                ));
            }
            let (
                Obj::FunctionSpace(FunctionSpace::FnSet(declared)),
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(next)),
            ) = (function.body.ret_set.as_ref(), expanded)
            else {
                return Err(invalid("GroupedReturnedLiteral"));
            };
            if !function_domains_alpha_equal(declared, &next.body) {
                return Err(invalid("GroupedReturnedSignature"));
            }
            current = expanded.clone();
            head_equal = format!("_grouped_eq_{index}");
        }
        Err(invalid("GroupedEmptyCall"))
    }

    fn compile_multivariable_reduction_node(
        &self,
        source: &Obj,
        steps: &[Step],
        cursor: &mut usize,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
        applied: Option<&AppliedBody<'_>>,
        depth: usize,
    ) -> Result<(Obj, String), LeanCompileError> {
        if depth >= 64 {
            return Err(invalid("Depth"));
        }
        let raw = |object| {
            if bindings.is_empty() {
                self.compile_normalization_value(object, position)
            } else {
                self.compile_function_raw_expression_bound(object, position, bindings)
            }
        };
        let unchanged = || {
            let value = raw(source)?;
            Ok((source.clone(), format!("(rfl : {value}={value})")))
        };
        if let Some(Step::ExactRational {
            source: saved,
            value,
        }) = steps.get(*cursor)
        {
            if saved == source {
                let (a, ha) = self.compile_eval_closed_value(saved, position)?;
                let (b, hb) = self.compile_eval_closed_value(value, position)?;
                if a != b {
                    return Err(invalid("ExactValue"));
                }
                *cursor += 1;
                return Ok((value.clone(), format!("(({ha}).trans ({hb}).symm)")));
            }
        }
        if *cursor == steps.len() {
            return unchanged();
        }
        if let Some(Step::FiniteSetEvaluation {
            source: saved,
            left,
            right,
            value,
        }) = steps.get(*cursor)
        {
            if saved == source {
                let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = source else {
                    return Err(invalid("FiniteSetSubject"));
                };
                let Obj::SetOperator(SetOperator::Intersect(intersection)) = size.set.as_ref()
                else {
                    return Err(invalid("FiniteSetSubject"));
                };
                let (Obj::SetFormer(SetFormer::ListSet(a)), Obj::SetFormer(SetFormer::ListSet(b))) =
                    (intersection.left.as_ref(), intersection.right.as_ref())
                else {
                    return Err(invalid("FiniteSetOperands"));
                };
                if a.list.len() != 1
                    || b.list.len() != 1
                    || EvalRational::from_obj(&a.list[0]).as_ref() != Some(left)
                    || EvalRational::from_obj(&b.list[0]).as_ref() != Some(right)
                {
                    return Err(invalid("FiniteSetOperands"));
                }
                let count = if left == right { 1 } else { 0 };
                let expected = EvalRational::new(count, 1).unwrap();
                if value != &expected.to_obj() {
                    return Err(invalid("FiniteSetValue"));
                }
                let (_, ha) = self.compile_eval_closed_value(&a.list[0], position)?;
                let (_, hb) = self.compile_eval_closed_value(&b.list[0], position)?;
                let (_, hv) = self.compile_eval_closed_value(value, position)?;
                let a = exact_rational_literal(left, "ℂ")?;
                let b = exact_rational_literal(right, "ℂ")?;
                let congruence = format!("(congrArg₂ (fun _left _right : M.Value => M.number (Litex.finiteCard (Litex.SetSemantics.sepValue (Litex.SetSemantics.insertValue _left Litex.SetSemantics.emptyValue) (fun _element => M.mem _element (Litex.SetSemantics.insertValue _right Litex.SetSemantics.emptyValue))) : ℂ)) {ha} {hb})");
                let card = if left == right {
                    format!("(Litex.finiteCardSingletonIntersectionSame (M.number {a}))")
                } else {
                    format!("(Litex.finiteCardSingletonIntersectionDifferent (M.number {a}) (M.number {b}) (fun _equal => (by norm_num : ({a} : ℂ) ≠ ({b} : ℂ)) (M.number_injective _equal)))")
                };
                let law = format!("(congrArg (fun _size : ℕ => M.number (_size : ℂ)) {card})");
                let cast = format!(
                    "(congrArg M.number (by norm_num : (({count} : ℕ) : ℂ) = {}))",
                    exact_rational_literal(&expected, "ℂ")?
                );
                *cursor += 1;
                return Ok((
                    value.clone(),
                    format!("(({congruence}).trans (({law}).trans (({cast}).trans ({hv}).symm)))"),
                ));
            }
        }
        if let Some(Step::PeriodicTrig {
            source: saved,
            proof,
        }) = steps.get(*cursor)
        {
            if saved == source {
                let term = self.compile_periodic_trig_reduction(source, proof, position)?;
                *cursor += 1;
                return Ok((proof.value.clone(), term));
            }
        }
        if let Obj::ArithmeticOperator(op) = source {
            let pair = match op {
                ArithmeticOperator::Add(p) => Some((&p.left, &p.right, "addValue")),
                ArithmeticOperator::Sub(p) => Some((&p.left, &p.right, "subValue")),
                ArithmeticOperator::Mul(p) => Some((&p.left, &p.right, "mulValue")),
                ArithmeticOperator::Div(p) => Some((&p.left, &p.right, "divValue")),
                ArithmeticOperator::Pow(p) => Some((&p.base, &p.exponent, "powValue")),
                _ => None,
            };
            if let Some((a, b, law)) = pair {
                let (left, hl) = self.compile_multivariable_reduction_node(
                    a,
                    steps,
                    cursor,
                    position,
                    bindings,
                    applied,
                    depth + 1,
                )?;
                let (right, hr) = self.compile_multivariable_reduction_node(
                    b,
                    steps,
                    cursor,
                    position,
                    bindings,
                    applied,
                    depth + 1,
                )?;
                let result = match op {
                    ArithmeticOperator::Add(_) => add_objs(left, right),
                    ArithmeticOperator::Sub(_) => sub_objs(left, right),
                    ArithmeticOperator::Mul(_) => mul_objs(left, right),
                    ArithmeticOperator::Div(_) => div_objs(left, right),
                    ArithmeticOperator::Pow(_) => {
                        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                            base: Box::new(left),
                            exponent: Box::new(right),
                        }))
                    }
                    _ => unreachable!(),
                };
                if result == *source {
                    return unchanged();
                }
                let step = format!("(congrArg₂ M.{law} {hl} {hr})");
                // Supported children are already reduced. Only a recorded root
                // step can follow their congruence. Revisiting the children would
                // incorrectly accept a tape that reordered sibling reductions.
                if matches!(steps.get(*cursor), Some(Step::ExactRational {source: saved,..}) if saved == &result)
                {
                    let (result, tail) = self.compile_multivariable_reduction_node(
                        &result,
                        steps,
                        cursor,
                        position,
                        bindings,
                        applied,
                        depth + 1,
                    )?;
                    return Ok((result, format!("({step}.trans {tail})")));
                }
                return Ok((result, step));
            }
            if let ArithmeticOperator::Neg(p) = op {
                let (arg, proof) = self.compile_multivariable_reduction_node(
                    &p.arg,
                    steps,
                    cursor,
                    position,
                    bindings,
                    applied,
                    depth + 1,
                )?;
                return Ok((
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) })),
                    format!("(congrArg M.negValue {proof})"),
                ));
            }
        }
        if let Some((kind, argument)) = crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction::from_expression(source) {
            use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
            let (value, equality) = self.compile_multivariable_reduction_node(
                argument, steps, cursor, position, bindings, applied, depth + 1,
            )?;
            let operation = match kind {
                K::Exp => "(Litex.realUnaryValue (M := M) Real.exp)",
                K::Ln => "(Litex.realUnaryValue (M := M) Real.log)",
                K::Sin => "(Litex.realUnaryValue (M := M) Real.sin)",
                K::Cos => "(Litex.realUnaryValue (M := M) Real.cos)",
                K::Sqrt => "(Litex.sqrtValue (M := M))",
            };
            let result = kind.apply(value);
            let step = format!("(congrArg {operation} {equality})");
            if matches!(steps.get(*cursor), Some(Step::PeriodicTrig {source: saved,..} | Step::ExactRational {source: saved,..}) if saved == &result) {
                let (result, tail) = self.compile_multivariable_reduction_node(
                    &result, steps, cursor, position, bindings, applied, depth + 1,
                )?;
                return Ok((result, format!("({step}.trans {tail})")));
            }
            return Ok((result, step));
        }
        if let Obj::FnObj(call) = source {
            let (mut current, mut proof) = self.compile_multivariable_reduction_node(
                &call_head(&call.head),
                steps,
                cursor,
                position,
                bindings,
                applied,
                depth + 1,
            )?;
            for group in &call.body {
                let mut arguments = Vec::new();
                let mut equalities = Vec::new();
                for argument in group {
                    let (value, equality) = self.compile_multivariable_reduction_node(
                        argument,
                        steps,
                        cursor,
                        position,
                        bindings,
                        applied,
                        depth + 1,
                    )?;
                    arguments.push(Box::new(value));
                    equalities.push(equality);
                }
                let argument_equality = if let [equality] = equalities.as_slice() {
                    equality.clone()
                } else {
                    format!(
                        "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) {})",
                        finite_vector_equality(&equalities)
                    )
                };
                if let Some(Step::NativeMatrixBeta {
                    source: callable,
                    arguments: recorded,
                    expanded,
                }) = steps.get(*cursor)
                {
                    if current == Obj::MatrixOperator(callable.operator.clone()) {
                        if call.body.len() != 1 || call_head(&call.head) != current
                            || bindings.keys().any(|id| crate::execute::execute_fact_stmt::multivariable::expression::depends_on(source, *id))
                            || applied.is_some()
                            || recorded.len() != arguments.len()
                            || recorded.iter().zip(&arguments).any(|(a,b)| a != b.as_ref()) {
                            return Err(invalid("NativeMatrixOriginalCall"));
                        }
                        if !callable.function.body.dom_facts.is_empty() {
                            return Err(invalid("NativeMatrixGuard"));
                        }
                        let step = position.with_visible_wd(source, &mut |wd, producer| {
                            let actual = self.compile_wd(wd, producer)?;
                            let (value, law) = self.compile_matrix_component_step(source,
                                "_matrix_reduction_call", callable, expanded,
                                Some((&arguments, &equalities)), wd, producer)?;
                            let input = self.compile_normalization_value(source, producer)?;
                            let endpoint = self.compile_normalization_value(expanded, producer)?;
                            Ok(format!("(let _matrix_reduction_call := {actual}; (show {input} = Litex.denote _matrix_reduction_call from rfl).trans (({law}).trans (show {value} = {endpoint} from rfl)))"))
                        })?.ok_or_else(|| invalid("NativeMatrixCallWD"))?;
                        *cursor += 1;
                        let (result, tail) = self.compile_multivariable_reduction_node(
                            expanded,
                            steps,
                            cursor,
                            position,
                            bindings,
                            applied,
                            depth + 1,
                        )?;
                        return Ok((result, format!("(({step}).trans {tail})")));
                    }
                }
                if let Some(Step::AnonymousBeta {
                    function,
                    arguments: recorded,
                    expanded,
                }) = steps.get(*cursor)
                {
                    if current == Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone())) {
                        if call.body.len() > 1 && call_head(&call.head) == current {
                            if !bindings.is_empty() {
                                return Err(invalid("GroupedCallContext"));
                            }
                            return with_original_call(
                                source,
                                position,
                                applied,
                                &mut |wd, producer| {
                                    self.compile_grouped_anonymous_reduction(
                                        source,
                                        wd,
                                        steps,
                                        cursor,
                                        &arguments,
                                        &equalities,
                                        producer,
                                        applied,
                                        depth,
                                    )
                                },
                            )?
                            .ok_or_else(|| invalid("GroupedCallWD"));
                        }
                        if call.body.len() != 1
                            || call_head(&call.head) != current
                            || !bindings.is_empty()
                        {
                            return Err(invalid("BetaOriginalCall"));
                        }
                        if !function.body.dom_facts.is_empty()
                            || recorded.len() != arguments.len()
                            || recorded
                                .iter()
                                .zip(&arguments)
                                .any(|(a, b)| a != b.as_ref())
                        {
                            return Err(invalid("BetaArguments"));
                        }
                        let mut emit = |wd: &ObjWellDefinedProof, original: &SourcePosition<'_>| {
                            let beta = self.compile_checked_function_beta(
                                wd.obj(),
                                wd,
                                function,
                                None,
                                expanded,
                                Some((&arguments, &equalities)),
                                original,
                            )?;
                            *cursor += 1;
                            let (result, tail) = if steps[*cursor..]
                                .iter()
                                .any(|s| matches!(s, Step::AnonymousBeta { .. }))
                            {
                                self.compile_applied_body_reduction(
                                    wd,
                                    expanded,
                                    &arguments,
                                    &equalities,
                                    steps,
                                    cursor,
                                    original,
                                    applied,
                                    depth + 1,
                                )?
                            } else {
                                self.compile_multivariable_reduction_node(
                                    expanded,
                                    steps,
                                    cursor,
                                    original,
                                    bindings,
                                    applied,
                                    depth + 1,
                                )?
                            };
                            Ok((result, format!("(({beta}).trans {tail})")))
                        };
                        let result = with_original_call(source, position, applied, &mut emit)?;
                        return result.ok_or_else(|| invalid("BetaCallWD"));
                    }
                }
                proof = format!("(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {proof} {argument_equality})");
                if let Some(Step::TupleProjection { tuple, index }) = steps.get(*cursor) {
                    if let Obj::ProductShape(ProductShape::Tuple(actual)) = &current {
                        if actual != tuple
                            || !matches!(arguments.as_slice(), [argument]
                                if literal_dimension(argument) == Some(*index))
                        {
                            return Err(invalid("TupleProjectionSubject"));
                        }
                        let offset = index
                            .checked_sub(1)
                            .ok_or_else(|| invalid("TupleProjectionIndex"))?;
                        let selected = tuple
                            .args
                            .get(offset)
                            .ok_or_else(|| invalid("TupleProjectionIndex"))?;
                        let values = tuple
                            .args
                            .iter()
                            .map(|value| raw(value))
                            .collect::<Result<Vec<_>, _>>()?;
                        let law = format!(
                            "(by let _tuple_values : Fin {arity} → M.Value := ![{}]; have _tuple_index : Litex.FiniteFunction.index (M := M) ({offset} : Fin {arity}) = M.number ({index} : ℂ) := (by norm_num [Litex.FiniteFunction.index]); exact (congrArg (Litex.FunctionSemantics.callValue (Litex.FiniteFunction.tupleValue _tuple_values)) _tuple_index.symm).trans (Litex.FiniteFunction.call_tuple _tuple_values ({offset} : Fin {arity})))",
                            values.join(", "), arity = values.len(),
                        );
                        proof = format!("(({proof}).trans {law})");
                        *cursor += 1;
                        // The producer selects this component without reducing
                        // it again. A later call group continues from it.
                        current = selected.as_ref().clone();
                        continue;
                    }
                }
                current = crate::execute::execute_fact_stmt::function_domain::function_application(
                    &current, arguments,
                )
                .map_err(|_| invalid("CallHead"))?;
            }
            return Ok((current, proof));
        }
        // Other tape variants require their own evidence consumers. No record
        // is silently skipped: the caller checks the final cursor and endpoint.
        unchanged()
    }
}
