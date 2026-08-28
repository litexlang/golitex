//! Fact transformations, definition reduction, and equality rewrite.

use super::super::*;
use super::result_alignment::facts_align_by_anonymous_function_beta_normalization_for_result_compiler;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_single_fact_transformation_from_result(
        &mut self,
        target: &Fact,
        transformation: &SuccessTransformFactResult,
    ) -> Result<Option<String>, String> {
        let source = transformation.source.fact();
        self.install_fact_anonymous_function_occurrence_aliases(
            target,
            "fact transformation target",
        )?;
        self.install_fact_anonymous_function_occurrence_aliases(
            &source,
            "fact transformation source",
        )?;
        let Some(source_proof) = self
            .construct_lean_proof_from_shared_verify_fact_result(transformation.source.as_ref())
            .map_err(|error| format!("fact transformation source proof: {error}"))?
        else {
            return Ok(None);
        };
        Ok(Some(
            self.construct_lean_fact_transformation_step_from_result(
                &source,
                target,
                source_proof,
                &transformation.rule,
                0,
            )
            .map_err(|error| format!("fact transformation replay: {error}"))?,
        ))
    }

    pub(in super::super) fn construct_lean_fact_transformation_step_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        source_proof: String,
        rule: &FactTransformationRule,
        step_index: usize,
    ) -> Result<String, String> {
        match rule {
            FactTransformationRule::RationalNormalization => {
                if membership_facts_are_equal_up_to_nested_binder_alpha(source, target)
                    || equality_facts_are_equal_up_to_nested_binder_alpha(source, target)
                    || subset_facts_are_equal_up_to_nested_binder_alpha(source, target)
                    || nonempty_facts_are_equal_up_to_nested_binder_alpha(source, target)
                    || normal_atomic_facts_are_equal_up_to_nested_binder_alpha(source, target)
                    || elementwise_forall_is_set_inclusion(source, target)
                    || elementwise_forall_is_set_inclusion(target, source)
                {
                    return Ok(source_proof);
                }
                if !facts_align_by_nested_rational_normalization_for_result_compiler(source, target)
                {
                    return Err(format!(
                        "fact transformation step {step_index} does not retain a rational-normalization shape"
                    ));
                }
                render_fact(source, &self.environment_stack)?;
                render_fact(target, &self.environment_stack)?;
                Ok(format!(
                    "(by\n  convert {source_proof} using 1 <;> norm_num)"
                ))
            }
            FactTransformationRule::AnonymousFunctionBetaNormalization => {
                if !facts_align_by_anonymous_function_beta_normalization_for_result_compiler(
                    source, target,
                )? {
                    return Err(format!(
                        "fact transformation step {step_index} does not retain an anonymous-function beta-normalization shape"
                    ));
                }
                // Neither frozen transformation endpoint is required to own
                // the parser occurrence selected for the enclosing statement
                // Result. The structural replay above validates the exact
                // beta step; the enclosing statement renderer supplies the
                // target proposition, and Lean checks this returned proof
                // against that definitionally reduced type.
                Ok(source_proof)
            }
            FactTransformationRule::EqualityRewrite(evidence) => self
                .construct_lean_equality_rewrite_transformation_from_result(
                    source,
                    target,
                    source_proof,
                    evidence,
                    step_index,
                ),
            FactTransformationRule::TransparentDefinitionReduction(evidence) => self
                .construct_lean_transparent_definition_reduction_from_result(
                    source,
                    target,
                    source_proof,
                    evidence,
                    step_index,
                ),
        }
    }

    pub(in super::super) fn construct_lean_transparent_definition_reduction_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        source_proof: String,
        evidence: &TransparentDefinitionReductionEvidence,
        transformation_step_index: usize,
    ) -> Result<String, String> {
        if evidence.definitions.is_empty() {
            return Err(format!(
                "transparent definition transformation step {transformation_step_index} retained no definitions"
            ));
        }
        let mut substitutions = HashMap::new();
        let mut definition_names = Vec::with_capacity(evidence.definitions.len());
        let mut seen_symbols = HashSet::new();
        for (definition_index, definition) in evidence.definitions.iter().enumerate() {
            let symbol_id = definition.symbol.id();
            if !seen_symbols.insert(symbol_id) {
                return Err(format!(
                    "transparent definition transformation step {transformation_step_index} repeats symbol ID {}",
                    symbol_id.value()
                ));
            }
            if !object_is_symbol(&definition.defining_equality.left, symbol_id)
                || obj_equality_key(&definition.defining_equality.right)
                    != obj_equality_key(&definition.definition_object)
            {
                return Err(format!(
                    "transparent definition {definition_index} changed its retained defining equality"
                ));
            }
            let defining_fact: Fact = definition.defining_equality.clone().into();
            resolve_fact_citation(
                &definition.defining_equality_fact_id,
                &defining_fact,
                &self.environment_stack,
            )?;
            let lean_name = self
                .environment_stack
                .symbol_names
                .get(&symbol_id)
                .ok_or_else(|| {
                    format!(
                        "transparent definition {definition_index} references unavailable symbol ID {}",
                        symbol_id.value()
                    )
                })?
                .clone();
            substitutions.insert(
                symbol_id.substitution_key(),
                definition.definition_object.clone(),
            );
            definition_names.push(lean_name);
        }

        let reduced_target = Runtime::default()
            .inst_fact(
                target,
                &substitutions,
                SubstitutionMode::TransparentDefinition,
                None,
            )
            .map_err(|error| {
                format!(
                    "transparent definition transformation step {transformation_step_index} could not replay its exact substitution: {}",
                    error.trace_message()
                )
            })?;
        let rendered_reduced_target = render_fact(&reduced_target, &self.environment_stack)?;
        let rendered_source = render_fact(source, &self.environment_stack)?;
        if rendered_reduced_target != rendered_source {
            return Err(format!(
                "transparent definition transformation step {transformation_step_index} reduced `{target}` to `{reduced_target}` instead of `{source}`"
            ));
        }
        render_fact(target, &self.environment_stack)?;
        Ok(format!(
            "(by\n  unfold {}\n  exact ({source_proof}))",
            definition_names.join(" ")
        ))
    }

    pub(in super::super) fn construct_lean_equality_rewrite_transformation_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        mut proof: String,
        evidence: &EqualityTransportEvidence,
        transformation_step_index: usize,
    ) -> Result<String, String> {
        if evidence.steps.is_empty() {
            return if source.to_string() == target.to_string() {
                Ok(proof)
            } else {
                Err(format!(
                    "fact transformation step {transformation_step_index} has an empty equality rewrite"
                ))
            };
        }

        if let Some(proof) = self
            .construct_lean_transparent_definition_equality_rewrite_from_result(
                source,
                target,
                &proof,
                evidence,
                transformation_step_index,
            )?
        {
            return Ok(proof);
        }

        match (source, target) {
            (
                Fact::AtomicFact(AtomicFact::InFact(source_membership)),
                Fact::AtomicFact(AtomicFact::InFact(target_membership)),
            ) => {
                if obj_equality_key(&source_membership.set)
                    != obj_equality_key(&target_membership.set)
                {
                    return Err("fact transformation equality rewrite changed its set".into());
                }
                let rendered_set = render_obj(&target_membership.set, &self.environment_stack)?;
                let mut current = source_membership.element.clone();
                for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
                    if obj_equality_key(&current) != obj_equality_key(&rewrite.from) {
                        return Err(format!(
                            "fact transformation equality rewrite {rewrite_index} does not start at the current member"
                        ));
                    }
                    let (equality_proof, forward) =
                        self.resolve_equality_rewrite_proof(rewrite, rewrite_index)?;
                    let direction = if forward { "mp" } else { "mpr" };
                    proof = format!(
                        "(Litex.In.congr ({equality_proof}) {rendered_set}).{direction} ({proof})"
                    );
                    current = rewrite.to.clone();
                }
                if obj_equality_key(&current) != obj_equality_key(&target_membership.element) {
                    return Err(
                        "fact transformation equality rewrite did not reach its target member"
                            .into(),
                    );
                }
                Ok(proof)
            }
            (
                Fact::AtomicFact(AtomicFact::EqualFact(source_equality)),
                Fact::AtomicFact(AtomicFact::EqualFact(target_equality)),
            ) => {
                let mut current_left = source_equality.left.clone();
                let mut current_right = source_equality.right.clone();
                for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
                    let rewrites_left =
                        obj_equality_key(&current_left) == obj_equality_key(&rewrite.from);
                    let rewrites_right =
                        obj_equality_key(&current_right) == obj_equality_key(&rewrite.from);
                    if rewrites_left == rewrites_right {
                        return Err(format!(
                            "fact transformation equality rewrite {rewrite_index} does not select exactly one equality endpoint"
                        ));
                    }
                    let (equality_proof, forward) =
                        self.resolve_equality_rewrite_proof(rewrite, rewrite_index)?;
                    let oriented_equality_proof = if forward {
                        equality_proof
                    } else {
                        format!("Litex.Same.symm ({equality_proof})")
                    };
                    if rewrites_left {
                        proof = format!(
                            "Litex.Same.trans (Litex.Same.symm ({oriented_equality_proof})) ({proof})"
                        );
                        current_left = rewrite.to.clone();
                    } else {
                        proof = format!("Litex.Same.trans ({proof}) ({oriented_equality_proof})");
                        current_right = rewrite.to.clone();
                    }
                }
                if obj_equality_key(&current_left) != obj_equality_key(&target_equality.left)
                    || obj_equality_key(&current_right) != obj_equality_key(&target_equality.right)
                {
                    return Err(
                        "fact transformation equality rewrite did not reach its target equality"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                Ok(proof)
            }
            (source_order, target_order)
                if order_relation_parts(source_order).is_ok()
                    && order_relation_parts(target_order).is_ok() =>
            {
                let (source_left, source_right, source_strict) =
                    order_relation_parts(source_order)?;
                let (target_left, target_right, target_strict) =
                    order_relation_parts(target_order)?;
                if source_strict != target_strict {
                    return Err(
                        "fact transformation equality rewrite changed order strictness".into(),
                    );
                }
                let mut current_left = source_left.clone();
                let mut current_right = source_right.clone();
                let mut rewrite_declarations = Vec::with_capacity(evidence.steps.len());
                let mut rewrite_names = Vec::with_capacity(evidence.steps.len());
                for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
                    let rewrites_left =
                        obj_equality_key(&current_left) == obj_equality_key(&rewrite.from);
                    let rewrites_right =
                        obj_equality_key(&current_right) == obj_equality_key(&rewrite.from);
                    if rewrites_left == rewrites_right {
                        return Err(format!(
                            "fact transformation equality rewrite {rewrite_index} does not select exactly one order endpoint"
                        ));
                    }
                    let (native_equality, forward, rendered_from, rendered_to) =
                        self.resolve_native_equality_rewrite_proof(rewrite, rewrite_index)?;
                    let oriented = if forward {
                        native_equality
                    } else {
                        format!("Eq.symm ({native_equality})")
                    };
                    let rewrite_name = format!("__native_rewrite{}", rewrite_index + 1);
                    rewrite_declarations.push(format!(
                        "  have {rewrite_name} : {} = {} := {oriented}",
                        rendered_from, rendered_to,
                    ));
                    rewrite_names.push(rewrite_name);
                    if rewrites_left {
                        current_left = rewrite.to.clone();
                    } else {
                        current_right = rewrite.to.clone();
                    }
                }
                if obj_equality_key(&current_left) != obj_equality_key(target_left)
                    || obj_equality_key(&current_right) != obj_equality_key(target_right)
                {
                    return Err(
                        "fact transformation equality rewrite did not reach its target order"
                            .into(),
                    );
                }
                let mut lines = vec!["(by".to_string()];
                lines.extend(rewrite_declarations);
                lines.push(format!("  have __transported := ({proof})"));
                lines.push(format!(
                    "  rw [{}] at __transported",
                    rewrite_names.join(", ")
                ));
                lines.push("  simpa [Litex.fnApplyOwn] using __transported)".to_string());
                Ok(lines.join("\n"))
            }
            _ => Err(format!(
                "fact transformation equality rewrite does not support `{source}` -> `{target}`"
            )),
        }
    }

    fn construct_lean_transparent_definition_equality_rewrite_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        source_proof: &str,
        evidence: &EqualityTransportEvidence,
        transformation_step_index: usize,
    ) -> Result<Option<String>, String> {
        let mut substitutions = HashMap::new();
        let mut definition_names = Vec::with_capacity(evidence.steps.len());
        let mut seen_symbols = HashSet::new();
        for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(&rewrite.equality.left)?
            else {
                return Ok(None);
            };
            let Some(definition) = self
                .environment_stack
                .transparent_object_definitions
                .get(&symbol_id)
            else {
                return Ok(None);
            };
            let equality_fact: Fact = rewrite.equality.clone().into();
            if definition.defining_equality_fact_id != rewrite.equality_fact_id
                || definition.defining_equality.to_string() != equality_fact.to_string()
                || obj_equality_key(&definition.value) != obj_equality_key(&rewrite.equality.right)
            {
                return Ok(None);
            }
            self.resolve_equality_rewrite_proof(rewrite, rewrite_index)?;
            if !seen_symbols.insert(symbol_id) {
                return Err(format!(
                    "fact transformation transparent equality rewrite step {transformation_step_index} repeats symbol ID {}",
                    symbol_id.value()
                ));
            }
            let lean_name = self
                .environment_stack
                .symbol_names
                .get(&symbol_id)
                .ok_or_else(|| {
                    format!(
                        "fact transformation transparent equality rewrite step {transformation_step_index} references unavailable symbol ID {}",
                        symbol_id.value()
                    )
                })?
                .clone();
            substitutions.insert(symbol_id.substitution_key(), definition.value.clone());
            definition_names.push(lean_name);
        }

        let reduced_source = Runtime::default()
            .inst_fact(
                source,
                &substitutions,
                SubstitutionMode::TransparentDefinition,
                None,
            )
            .map_err(|error| {
                format!(
                    "fact transformation transparent equality rewrite step {transformation_step_index} could not reduce its source: {}",
                    error.trace_message()
                )
            })?;
        let reduced_target = Runtime::default()
            .inst_fact(
                target,
                &substitutions,
                SubstitutionMode::TransparentDefinition,
                None,
            )
            .map_err(|error| {
                format!(
                    "fact transformation transparent equality rewrite step {transformation_step_index} could not reduce its target: {}",
                    error.trace_message()
                )
            })?;
        if render_fact(&reduced_source, &self.environment_stack)?
            != render_fact(&reduced_target, &self.environment_stack)?
        {
            return Err(format!(
                "fact transformation transparent equality rewrite step {transformation_step_index} does not reduce its source and target to the same proposition"
            ));
        }
        render_fact(source, &self.environment_stack)?;
        render_fact(target, &self.environment_stack)?;
        Ok(Some(format!(
            "(by\n  simpa [{}] using ({source_proof}))",
            definition_names.join(", ")
        )))
    }

    pub(in super::super) fn resolve_equality_rewrite_proof(
        &self,
        rewrite: &EqualityTransportStep,
        rewrite_index: usize,
    ) -> Result<(String, bool), String> {
        let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
        let fact_id = rewrite.equality_fact_id;
        let proof = resolve_fact_citation(&fact_id, &equality_fact, &self.environment_stack)?;
        let left = obj_equality_key(&rewrite.equality.left);
        let right = obj_equality_key(&rewrite.equality.right);
        let from = obj_equality_key(&rewrite.from);
        let to = obj_equality_key(&rewrite.to);
        if from == left && to == right {
            Ok((proof, true))
        } else if from == right && to == left {
            Ok((proof, false))
        } else {
            Err(format!(
                "fact transformation equality rewrite {rewrite_index} is not oriented by its retained equality"
            ))
        }
    }

    pub(in super::super) fn resolve_native_equality_rewrite_proof(
        &self,
        rewrite: &EqualityTransportStep,
        rewrite_index: usize,
    ) -> Result<(String, bool, String, String), String> {
        let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
        let binding = self
            .environment_stack
            .native_equality_proofs
            .get(&rewrite.equality_fact_id)
            .ok_or_else(|| {
                format!(
                    "fact transformation equality rewrite {rewrite_index} cites `{}` without a verifier-backed native Lean equality certificate",
                    rewrite.equality_fact_id
                )
            })?;
        if binding.fact.to_string() != equality_fact.to_string() {
            return Err(format!(
                "fact transformation equality rewrite {rewrite_index} changed the native equality proposition for `{}`",
                rewrite.equality_fact_id
            ));
        }
        let left = obj_equality_key(&rewrite.equality.left);
        let right = obj_equality_key(&rewrite.equality.right);
        let from = obj_equality_key(&rewrite.from);
        let to = obj_equality_key(&rewrite.to);
        if from == left && to == right {
            Ok((
                binding.proof_expression.clone(),
                true,
                binding.rendered_left.clone(),
                binding.rendered_right.clone(),
            ))
        } else if from == right && to == left {
            Ok((
                binding.proof_expression.clone(),
                false,
                binding.rendered_right.clone(),
                binding.rendered_left.clone(),
            ))
        } else {
            Err(format!(
                "fact transformation native equality rewrite {rewrite_index} is not oriented by its retained equality"
            ))
        }
    }
}
