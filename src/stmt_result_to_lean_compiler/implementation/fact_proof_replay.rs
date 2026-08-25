use super::*;

impl StmtResultToLeanCompiler {
    pub(super) fn construct_lean_set_builtin_from_result(
        &mut self,
        target: &Fact,
        rule: SetBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if matches!(
            rule,
            SetBuiltinRule::SubsetReflexivity | SetBuiltinRule::SupersetReflexivity
        ) {
            if !subgoals.is_empty() {
                return Err("set-relation reflexivity unexpectedly gained child Results".into());
            }
            return Ok(Some(render_set_relation_reflexivity(
                target,
                rule == SetBuiltinRule::SubsetReflexivity,
                &self.environment_stack,
            )?));
        }
        if matches!(
            rule,
            SetBuiltinRule::UnionCommutative
                | SetBuiltinRule::UnionAssociative
                | SetBuiltinRule::UnionIdempotent
                | SetBuiltinRule::UnionEmptyIdentity
                | SetBuiltinRule::IntersectCommutative
                | SetBuiltinRule::IntersectAssociative
        ) {
            if !subgoals.is_empty() {
                return Err("structural set equality unexpectedly gained child Results".into());
            }
            let compatibility_rule = match rule {
                SetBuiltinRule::UnionCommutative => LeanSetBuiltinCompilationKind::UnionCommutative,
                SetBuiltinRule::UnionAssociative => LeanSetBuiltinCompilationKind::UnionAssociative,
                SetBuiltinRule::UnionIdempotent => LeanSetBuiltinCompilationKind::UnionIdempotent,
                SetBuiltinRule::UnionEmptyIdentity => {
                    LeanSetBuiltinCompilationKind::UnionEmptyIdentity
                }
                SetBuiltinRule::IntersectCommutative => {
                    LeanSetBuiltinCompilationKind::IntersectCommutative
                }
                SetBuiltinRule::IntersectAssociative => {
                    LeanSetBuiltinCompilationKind::IntersectAssociative
                }
                _ => unreachable!("matched structural set rule"),
            };
            return Ok(Some(render_structural_set_equality(
                target,
                compatibility_rule,
                &self.environment_stack,
            )?));
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("set builtin child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("set builtin child {index} published effects"));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            children.push((child.fact(), proof));
        }
        Ok(Some(render_base_set_builtin_rule_from_compiled_children(
            target,
            rule,
            &children,
            &self.environment_stack,
        )?))
    }

    /// `Reuse` / `Combine`: every edge cites the exact previously stored
    /// equality FactId retained by the verifier. No proposition lookup or
    /// equality-graph search is repeated in the compiler.
    pub(super) fn construct_lean_known_equality_path_from_result(
        &self,
        target: &Fact,
        evidence: &KnownEqualityBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() || !subgoals.is_empty() {
            return Err("known-equality path changed its target or gained child Results".into());
        }
        let (target_left, target_right) = equality_parts(target)?;
        if evidence.steps.is_empty() {
            return Err("known-equality path retained no steps".into());
        }
        let mut current_key = obj_equality_key(target_left);
        let target_key = obj_equality_key(target_right);
        let mut accumulated: Option<String> = None;
        for (index, step) in evidence.steps.iter().enumerate() {
            if current_key != obj_equality_key(&step.from) {
                return Err(format!("known-equality path step {index} is disconnected"));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let reverse = if from_key == left_key && to_key == right_key {
                false
            } else if from_key == right_key && to_key == left_key {
                true
            } else {
                return Err(format!(
                    "known-equality path step {index} has invalid orientation"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let cited = resolve_fact_citation(
                &step.source_fact_id,
                &equality_fact,
                &self.environment_stack,
            )?;
            let oriented = if reverse {
                format!("Litex.Same.symm ({cited})")
            } else {
                cited
            };
            accumulated = Some(match accumulated {
                None => oriented,
                Some(previous) => format!("Litex.Same.trans ({previous}) ({oriented})"),
            });
            current_key = to_key;
        }
        if current_key != target_key {
            return Err("known-equality path does not end at its target".into());
        }
        render_fact(target, &self.environment_stack)?;
        accumulated.ok_or_else(|| "known-equality path retained no proof".into())
    }

    /// `PassThrough`: subset/superset dual spellings lower to the same Lean
    /// proposition. The one exact child Result therefore supplies the proof,
    /// while the typed rule fixes which source-level conversion occurred.
    pub(super) fn construct_lean_set_relation_duality_from_result(
        &mut self,
        target: &Fact,
        rule: SetRelationDualityBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [child] = subgoals else {
            return Err("set-relation duality requires one child Result".into());
        };
        let child = child
            .factual_success()
            .ok_or_else(|| "set-relation duality child is not factual".to_string())?;
        if !child.store.infers.is_empty() {
            return Err("set-relation duality child published effects".into());
        }
        let (target_left, target_right, target_negated, target_is_subset_spelling) =
            normalized_set_relation_parts(target)?;
        let child_fact = child.fact();
        let (child_left, child_right, child_negated, child_is_subset_spelling) =
            normalized_set_relation_parts(&child_fact)?;
        let expected_target_subset_spelling = match rule {
            SetRelationDualityBuiltinRule::SubsetFromSuperset
            | SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => true,
            SetRelationDualityBuiltinRule::SupersetFromSubset
            | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => false,
        };
        let expected_negated = matches!(
            rule,
            SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset
                | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset
        );
        if target_is_subset_spelling != expected_target_subset_spelling
            || child_is_subset_spelling == target_is_subset_spelling
            || target_negated != expected_negated
            || child_negated != expected_negated
            || obj_equality_key(target_left) != obj_equality_key(child_left)
            || obj_equality_key(target_right) != obj_equality_key(child_right)
        {
            return Err("set-relation duality changed its orientation or endpoints".into());
        }
        if render_fact(target, &self.environment_stack)?
            != render_fact(&child_fact, &self.environment_stack)?
        {
            return Err("set-relation duality no longer lowers to one Lean proposition".into());
        }
        self.construct_lean_proof_from_direct_fact_result(child)
    }

    /// `Wrap`: cite the exact source FactId, then apply the verifier-retained
    /// equality edges in their recorded order. The Result owns both the
    /// orientation and the equality FactId of every edge; the compiler does
    /// not search the current environment for a proposition-shaped match.
    pub(super) fn construct_lean_fact_citation_with_equality_transport_from_result(
        &self,
        target: &Fact,
        cited_statement: &Stmt,
        source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
    ) -> Result<Option<String>, String> {
        let Stmt::Fact(source_fact) = cited_statement else {
            return Ok(None);
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(None);
        };
        let mut proof =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        if equality_transport_has_no_steps(equality_transport) {
            if facts_are_comparison_notation_duals(source_fact, target)
                && render_fact(source_fact, &self.environment_stack)?
                    == render_fact(target, &self.environment_stack)?
            {
                return Ok(Some(proof));
            }
            return Ok(Some(resolve_fact_citation(
                &source_fact_id,
                target,
                &self.environment_stack,
            )?));
        }

        let (source_element, source_set) = membership_parts(source_fact)?;
        let mut current_element = source_element.clone();
        let (target_element, target_set) = membership_parts(target)?;
        if obj_equality_key(source_set) != obj_equality_key(target_set) {
            return Err("equality transport changed the membership set".into());
        }
        let rendered_set = render_obj(target_set, &self.environment_stack)?;
        for (step_index, step) in equality_transport
            .expect("nonempty transport checked above")
            .steps
            .iter()
            .enumerate()
        {
            if obj_equality_key(&current_element) != obj_equality_key(&step.from) {
                return Err(format!(
                    "equality transport step {step_index} does not start at the current membership element"
                ));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let direction = if from_key == left_key && to_key == right_key {
                "mp"
            } else if from_key == right_key && to_key == left_key {
                "mpr"
            } else {
                return Err(format!(
                    "equality transport step {step_index} is not oriented by its retained equality"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let equality_fact_id = step.equality_fact_id;
            let equality_proof =
                resolve_fact_citation(&equality_fact_id, &equality_fact, &self.environment_stack)?;
            proof =
                format!("(Litex.In.congr ({equality_proof}) {rendered_set}).{direction} ({proof})");
            current_element = step.to.clone();
        }
        if obj_equality_key(&current_element) != obj_equality_key(target_element) {
            return Err("equality transport did not end at the target membership element".into());
        }
        Ok(Some(proof))
    }

    pub(super) fn construct_lean_stored_fact_citation_proof_from_result(
        &self,
        target: &Fact,
        citation: &SuccessStoredFactCitationProofResult,
    ) -> Result<Option<String>, String> {
        self.construct_lean_fact_citation_with_equality_transport_from_result(
            target,
            &citation.source_fact.clone().into_stmt(),
            Some(citation.source_fact_id),
            None,
        )
    }

    /// `Leaf`: replay the verifier-selected one-step unfolding of a checked
    /// named function. The defining equality is resolved by exact `FactId`;
    /// the application orientation and reduced body come from the Result.
    pub(super) fn construct_lean_checked_function_definition_reduction_from_result(
        &self,
        target: &Fact,
        reduction: &CheckedFunctionDefinitionReductionEvidence,
    ) -> Result<String, String> {
        let (target_left, target_right) = equality_parts(target)?;
        let (expected_application, expected_other) = if reduction.application_is_left {
            (target_left, target_right)
        } else {
            (target_right, target_left)
        };
        if obj_equality_key(expected_application) != obj_equality_key(&reduction.application_side)
            || obj_equality_key(expected_other) != obj_equality_key(&reduction.other_side)
        {
            return Err(
                "checked function-definition reduction changed its goal orientation".into(),
            );
        }
        if !reduction.reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(
                &reduction.reduced,
                &reduction.other_side,
            )
        {
            return Err("checked function-definition reduction changed its reduced result".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) =
            &reduction.defining_equality
        else {
            return Err("checked function-definition source is not an equality".into());
        };
        if obj_equality_key(&defining_equality.left)
            != obj_equality_key(&reduction.definition_object)
            || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
        {
            return Err(
                "checked function-definition source changed its named-function definition".into(),
            );
        }
        resolve_fact_citation(
            &reduction.defining_equality_fact_id,
            &reduction.defining_equality,
            &self.environment_stack,
        )?;
        let binding = self
            .environment_stack
            .named_function_definitions
            .get(&reduction.defining_equality_fact_id)
            .ok_or_else(|| {
                format!(
                    "checked function-definition reduction references unavailable defining FactId `{}`",
                    reduction.defining_equality_fact_id
                )
            })?;
        if !object_is_symbol(&reduction.definition_object, binding.symbol_id) {
            return Err(
                "checked function-definition reduction changed its named function symbol".into(),
            );
        }
        let application_side = if reduction.application_is_left {
            LeanEqualityApplicationSide::Left
        } else {
            LeanEqualityApplicationSide::Right
        };
        render_checked_identity_function_reduction_from_fact(
            target,
            reduction.defining_equality_fact_id,
            application_side,
            &self.environment_stack,
        )
    }

    pub(super) fn construct_lean_single_fact_transformation_from_result(
        &mut self,
        target: &Fact,
        transformation: &SuccessTransformFactResult,
    ) -> Result<Option<String>, String> {
        let source = transformation.source.fact();
        let Some(source_proof) = self
            .construct_lean_proof_from_shared_verify_fact_result(transformation.source.as_ref())?
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
            )?,
        ))
    }

    pub(super) fn construct_lean_fact_transformation_step_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        source_proof: String,
        rule: &FactTransformationRule,
        step_index: usize,
    ) -> Result<String, String> {
        match rule {
            FactTransformationRule::RationalNormalization => {
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
            FactTransformationRule::EqualityRewrite(evidence) => self
                .construct_lean_equality_rewrite_transformation_from_result(
                    source,
                    target,
                    source_proof,
                    evidence,
                    step_index,
                ),
        }
    }

    pub(super) fn construct_lean_equality_rewrite_transformation_from_result(
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
            _ => Err(format!(
                "fact transformation equality rewrite does not support `{source}` -> `{target}`"
            )),
        }
    }

    pub(super) fn resolve_equality_rewrite_proof(
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

    /// `Wrap`: compile the one exact source-membership child first and then
    /// apply the fixed standard-set inclusion chain selected by the retained
    /// source and target sets. This consumes the recursive Result directly;
    /// no diagnostic label or compatibility proof IR participates.
    pub(super) fn construct_lean_standard_set_membership_projection_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [source_result] = subgoals else {
            return Err(
                "standard-set membership projection requires exactly one child Result".into(),
            );
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "standard-set membership projection child is not factual".to_string())?;
        let source = source_result.fact();
        if source_result.store.fact.to_string() != source.to_string()
            || !source_result.store.infers.is_empty()
        {
            return Err(
                "standard-set membership projection child changed its fact or published effects"
                    .into(),
            );
        }
        let (target_element, target_set) = membership_parts(target)?;
        let (source_element, source_set) = membership_parts(&source)?;
        if obj_equality_key(target_element) != obj_equality_key(source_element) {
            return Err("standard-set membership projection changed its source element".into());
        }
        let (Obj::StandardSet(source_set), Obj::StandardSet(target_set)) = (source_set, target_set)
        else {
            return Err("standard-set membership projection retained a nonstandard set".into());
        };
        let Some(mut proof) = self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        for theorem in standard_set_membership_projection_theorem_chain(*source_set, *target_set)? {
            proof = format!("Litex.Rules.{theorem} ({proof})");
        }
        Ok(Some(proof))
    }

    /// `Combine`: resolve the retained source forall by its exact FactId,
    /// compile each parameter/domain requirement from its recursive Result,
    /// and apply the already-emitted Lean theorem. The fresh Runtime below is
    /// used only as the kernel's stateless syntax-substitution utility; it has
    /// no executed environment and cannot rediscover a proof or FactId.
    pub(super) fn construct_lean_known_forall_instantiation_from_result(
        &mut self,
        target: &Fact,
        result: &SuccessInstantiateKnownForallResult,
    ) -> Result<Option<String>, String> {
        let source_fact = &result.source_fact;
        let Fact::ForallFact(source_forall) = source_fact else {
            return Err("known-forall Result cited a non-forall fact".into());
        };
        let source_fact_id = result.source_fact_id;
        let source_theorem =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if source_parameters.len() != result.instantiation.len() {
            return Err("known-forall Result changed its argument arity".into());
        }
        if result.requirements.len() != source_parameters.len() + source_forall.dom_facts.len() {
            return Err(
                "known-forall Result changed its parameter/domain requirement arity".into(),
            );
        }

        let arguments = result
            .instantiation
            .iter()
            .zip(source_parameters.iter())
            .map(|(item, (binding, _))| {
                if item.param != binding.name() || item.arg != item.arg_obj.to_string() {
                    return Err(
                        "known-forall Result changed its retained parameter order or argument"
                            .to_string(),
                    );
                }
                Ok(item.arg_obj.clone())
            })
            .collect::<Result<Vec<_>, String>>()?;
        let substitutions = source_forall
            .typed_parameters
            .param_defs_and_args_to_param_to_arg_map(&arguments);
        let substitution_runtime = Runtime::new();

        let mut application_terms = vec![source_theorem];
        for (parameter_index, (((_, parameter_type), argument), requirement)) in source_parameters
            .iter()
            .zip(arguments.iter())
            .zip(result.requirements.iter().take(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::ParameterType {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its kind"
                ));
            }
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall parameter requirement {parameter_index} is not factual")
            })?;
            if requirement_result.fact().to_string() != requirement.stmt.to_string() {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its fact"
                ));
            }
            validate_scoped_fact_check_result(
                requirement_result,
                &requirement.stmt,
                &format!("known-forall parameter requirement {parameter_index}"),
            )?;

            application_terms.push(render_obj(argument, &self.environment_stack)?);
            let requirement_needs_proof = match parameter_type {
                ParamType::Set(_) => {
                    let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = &requirement.stmt else {
                        return Err(
                            "known-forall set argument retained a non-set requirement".into()
                        );
                    };
                    if obj_equality_key(&sethood.set) != obj_equality_key(argument) {
                        return Err("known-forall set requirement changed its argument".into());
                    }
                    false
                }
                ParamType::Obj(source_set) => {
                    let instantiated_set = substitution_runtime
                        .inst_obj(source_set, &substitutions, SubstitutionMode::Exact)
                        .map_err(|error| {
                            format!("known-forall parameter substitution failed: {error:?}")
                        })?;
                    let (requirement_argument, requirement_set) =
                        membership_parts(&requirement.stmt)?;
                    if obj_equality_key(requirement_argument) != obj_equality_key(argument)
                        || obj_equality_key(requirement_set) != obj_equality_key(&instantiated_set)
                    {
                        return Err(
                            "known-forall object requirement changed its argument or carrier"
                                .into(),
                        );
                    }
                    true
                }
                ParamType::NonemptySet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property)) =
                        &requirement.stmt
                    else {
                        return Err(
                            "known-forall nonempty-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall nonempty-set requirement changed its argument".into()
                        );
                    }
                    true
                }
                ParamType::FiniteSet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property)) = &requirement.stmt
                    else {
                        return Err(
                            "known-forall finite-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall finite-set requirement changed its argument".into()
                        );
                    }
                    true
                }
            };
            if requirement_needs_proof {
                let Some(proof) =
                    self.construct_lean_proof_from_direct_fact_result(requirement_result)?
                else {
                    return Ok(None);
                };
                application_terms.push(format!("({proof})"));
            }
        }

        for (domain_index, (source_domain, requirement)) in source_forall
            .dom_facts
            .iter()
            .zip(result.requirements.iter().skip(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::Domain {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its kind"
                ));
            }
            let expected_domain = substitution_runtime
                .inst_fact(source_domain, &substitutions, SubstitutionMode::Exact, None)
                .map_err(|error| format!("known-forall domain substitution failed: {error:?}"))?;
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall domain requirement {domain_index} is not factual")
            })?;
            if requirement.stmt.to_string() != expected_domain.to_string()
                || requirement_result.fact().to_string() != expected_domain.to_string()
            {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its instantiated fact"
                ));
            }
            validate_scoped_fact_check_result(
                requirement_result,
                &expected_domain,
                &format!("known-forall domain requirement {domain_index}"),
            )?;
            let Some(proof) =
                self.construct_lean_proof_from_direct_fact_result(requirement_result)?
            else {
                return Ok(None);
            };
            application_terms.push(format!("({proof})"));
        }

        let then_fact_index = result.source_conclusion_location.then_fact_index();
        let source_then_fact = source_forall
            .then_facts
            .get(then_fact_index)
            .ok_or_else(|| "known-forall Result selected a missing then fact".to_string())?;
        let (source_conclusion, component_projection) = match result.source_conclusion_location {
            ForallConclusionLocation::DirectThenFact(_) => {
                (source_then_fact.clone().to_fact(), None)
            }
            ForallConclusionLocation::AndFactComponent(location) => {
                let ExistOrAndChainAtomicFact::AndFact(and_fact) = source_then_fact else {
                    return Err(
                        "known-forall Result selected an and component from a non-and conclusion"
                            .into(),
                    );
                };
                let component = and_fact
                    .facts
                    .get(location.component_index)
                    .ok_or_else(|| {
                        "known-forall Result selected a missing and component".to_string()
                    })?;
                (
                    Fact::from(component.clone()),
                    Some((location.component_index, and_fact.facts.len())),
                )
            }
            ForallConclusionLocation::ChainFactComponent(location) => {
                let ExistOrAndChainAtomicFact::ChainFact(chain_fact) = source_then_fact else {
                    return Err(
                            "known-forall Result selected a chain component from a non-chain conclusion"
                                .into(),
                        );
                };
                let components = chain_fact
                    .facts()
                    .map_err(|error| format!("known-forall source chain is invalid: {error:?}"))?;
                let component = components.get(location.component_index).ok_or_else(|| {
                    "known-forall Result selected a missing chain component".to_string()
                })?;
                (
                    Fact::from(component.clone()),
                    Some((location.component_index, components.len())),
                )
            }
        };
        let instantiated_conclusion = substitution_runtime
            .inst_fact(
                &source_conclusion,
                &substitutions,
                SubstitutionMode::Exact,
                None,
            )
            .map_err(|error| format!("known-forall conclusion substitution failed: {error:?}"))?;
        let mut application = format!("({})", application_terms.join(" "));
        let then_projection =
            conjunction_selector(then_fact_index, source_forall.then_facts.len())?;
        application.push_str(&then_projection);
        if let Some((component_index, component_count)) = component_projection {
            application.push_str(&conjunction_selector(component_index, component_count)?);
        }
        if instantiated_conclusion.to_string() == target.to_string() {
            return Ok(Some(application));
        }
        if facts_align_by_nested_rational_normalization_for_result_compiler(
            &instantiated_conclusion,
            target,
        ) {
            render_fact(target, &self.environment_stack)?;
            return Ok(Some(format!(
                "(by\n  convert {application} using 1 <;> norm_num)"
            )));
        }
        Err(format!(
            "known-forall instance `{instantiated_conclusion}` does not match target `{target}`"
        ))
    }

    /// `Wrap`: the arithmetic-closure Result owns exactly one conjunction
    /// child Result. The child retains the two ordered operand memberships;
    /// no diagnostic label or rebuilt verifier search participates here.
    pub(super) fn construct_lean_real_arithmetic_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: RealArithmeticMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
            return Err("real arithmetic membership Result changed its target carrier".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (RealArithmeticMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Sub, Obj::Sub(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexSubInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Div, Obj::Div(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexDivInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Pow, _) => return Ok(None),
            _ => {
                return Err("real arithmetic membership Result changed its source operator".into());
            }
        };
        let [components] = subgoals else {
            return Err(
                "real arithmetic membership Result must retain one conjunction child".into(),
            );
        };
        let components = components
            .factual_success()
            .ok_or_else(|| "real arithmetic membership child is not factual".to_string())?;
        if !components.store.infers.is_empty() || components.store.fact_id.is_some() {
            return Err(
                "real arithmetic membership conjunction child unexpectedly published effects"
                    .into(),
            );
        }
        let retained_components = conjunction_components(&components.fact())?;
        if retained_components.len() != 2 {
            return Err("real arithmetic membership child is not a binary conjunction".into());
        }
        for (retained, expected_operand) in
            retained_components.iter().zip([left, right].into_iter())
        {
            let (retained_element, retained_set) = membership_parts(retained)?;
            if !matches!(retained_set, Obj::StandardSet(StandardSet::R))
                || obj_equality_key(retained_element) != obj_equality_key(expected_operand)
            {
                return Err("real arithmetic membership child changed its ordered operands".into());
            }
        }
        let components_proof = self
            .construct_lean_proof_from_direct_fact_result(components)?
            .ok_or_else(|| {
                "real arithmetic membership conjunction has no direct recursive Result proof adapter"
                    .to_string()
            })?;
        let components_type = render_fact(&components.fact(), &self.environment_stack)?;
        let left_proof =
            render_real_operand_membership(left, "__components.1", &self.environment_stack);
        let right_proof =
            render_real_operand_membership(right, "__components.2", &self.environment_stack);
        Ok(Some(format!(
            "(by\n  have __components : {components_type} := {components_proof}\n  exact Litex.Rules.{theorem} ({left_proof}) ({right_proof}))"
        )))
    }

    pub(super) fn construct_lean_disjunction_introduction_from_result(
        &mut self,
        target: &Fact,
        evidence: &DisjunctionIntroductionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("disjunction-introduction evidence changed its target".into());
        }
        let branches = disjunction_components(target)?;
        let Some(selected) = branches.get(evidence.selected_index) else {
            return Err("disjunction-introduction evidence selected no target branch".into());
        };
        if selected.to_string() != evidence.expected_selected.to_string() {
            return Err("disjunction-introduction evidence changed its selected branch".into());
        }
        let [selected_result] = subgoals else {
            return Err(
                "disjunction-introduction evidence must retain one selected child Result".into(),
            );
        };
        let selected_result = selected_result
            .factual_success()
            .ok_or_else(|| "disjunction selected child is not factual".to_string())?;
        if selected_result.fact().to_string() != selected.to_string()
            || !selected_result.store.infers.is_empty()
        {
            return Err("disjunction selected child changed its proposition or effects".into());
        }
        let Some(selected_proof) =
            self.construct_lean_proof_from_direct_fact_result(selected_result)?
        else {
            return Ok(None);
        };
        Ok(Some(right_associated_disjunction_injection(
            selected_proof,
            evidence.selected_index,
            branches.len(),
        )?))
    }

    /// `Combine`: unfold the exact active concrete predicate proof retained as
    /// the sole child, then select the existential definition clause matching
    /// this Result's target. No Runtime lookup or label reconstruction occurs.
    pub(super) fn construct_lean_definition_projection_from_result(
        &mut self,
        target: &Fact,
        evidence: &DefinitionProjectionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let Fact::ExistFact(target_existential) = target else {
            return Err("definition projection requires an existential target".into());
        };
        if !target_existential.is_plain_exist() {
            return Ok(None);
        }
        let [source_result] = subgoals else {
            return Err(
                "definition projection must retain exactly one predicate source Result".into(),
            );
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "definition projection source child is not factual".to_string())?;
        let source_fact: Fact = evidence.fact.clone().into();
        if source_result.fact().to_string() != source_fact.to_string()
            || !source_result.store.infers.is_empty()
        {
            return Err("definition projection changed its predicate source child".into());
        }

        let definition_name = evidence.definition.name.clone();
        if evidence.fact.predicate.to_string() != definition_name {
            return Err("definition projection evidence names a different predicate".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "definition projection references unavailable predicate `{definition_name}`"
                )
            })?;
        let Some(active_definition) = &binding.definition else {
            return Err("definition projection selected an abstract predicate".into());
        };
        if active_definition.to_string() != evidence.definition.to_string() {
            return Err(
                "definition projection does not match the active predicate definition".into(),
            );
        }

        let components =
            instantiated_predicate_components(&source_fact, &binding, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let clause_index = components
            .iter()
            .position(|component| component == &rendered_target)
            .ok_or_else(|| {
                "definition projection target is not an instantiated definition component"
                    .to_string()
            })?;
        let selector = conjunction_selector(clause_index, components.len())?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!(
            "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  exact __definition{selector})",
            binding.lean_name
        )))
    }

    /// `Combine`: consume the base-membership child followed by every checked
    /// set-builder predicate child in source order. The representative used by
    /// Lean is introduced only inside the resulting proof term; the caller's
    /// compiler environment is unchanged.
    pub(super) fn construct_lean_set_builder_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &SetBuilderMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("set-builder membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("set-builder membership lost an ordered child Result".into());
        }
        let mut compiled_children = Vec::with_capacity(subgoals.len());
        for (index, (child, expected)) in subgoals
            .iter()
            .zip(evidence.expected_premises.iter())
            .enumerate()
        {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("set-builder child {index} is not factual"))?;
            if child.fact().to_string() != expected.to_string()
                || child.store.fact.to_string() != expected.to_string()
                || !child.store.infers.is_empty()
            {
                return Err(format!(
                    "set-builder child {index} changed its proposition or published effects"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            compiled_children.push((expected.clone(), proof));
        }
        Ok(Some(render_set_builder_membership_from_fact_and_proofs(
            target,
            &compiled_children,
            &self.environment_stack,
        )?))
    }

    /// `Wrap`: validate the exact pointwise forall child retained by the
    /// verifier, then package the compiler-constructed function value in the
    /// exact Lean carrier of its function set. The pointwise child is not
    /// discarded: its recursive `ForallProof` shape must agree with the
    /// evidence. The final `In.own` is possible only because rendering the
    /// function value already consumes its Result-owned WD/body evidence and
    /// constructs a value of that exact carrier.
    pub(super) fn construct_lean_function_set_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionSetMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-set membership evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-set membership evidence targets a non-membership".into());
        };
        if !matches!(&target_membership.set, Obj::FnSet(_)) {
            return Err("function-set membership evidence retained a non-function set".into());
        }
        let [pointwise_result] = subgoals else {
            return Err(
                "function-set membership evidence requires one pointwise forall child Result"
                    .into(),
            );
        };
        let pointwise_result = pointwise_result
            .factual_success()
            .ok_or_else(|| "function-set membership pointwise child is not factual".to_string())?;
        if pointwise_result.fact().to_string() != evidence.expected_pointwise.to_string()
            || pointwise_result.store.fact.to_string() != evidence.expected_pointwise.to_string()
        {
            return Err("function-set membership changed its pointwise proposition".into());
        }
        let Fact::ForallFact(expected_pointwise) = &evidence.expected_pointwise else {
            return Err(
                "function-set membership retained a non-forall pointwise proposition".into(),
            );
        };
        let SuccessFactProofResult::ForallProof(pointwise_proof) = pointwise_result.proof() else {
            return Err(
                "function-set membership pointwise child lost its ForallProof Result".into(),
            );
        };
        if pointwise_proof.forall_fact.to_string() != expected_pointwise.to_string()
            || pointwise_proof.proves.len() != expected_pointwise.then_facts.len()
        {
            return Err(
                "function-set membership pointwise ForallProof changed its binder or conclusions"
                    .into(),
            );
        }

        let rendered_function = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_function_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_rendered_target =
            format!("Litex.In {rendered_function} {rendered_function_set}");
        if rendered_target != expected_rendered_target {
            return Err("function-set membership changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_function_set} {rendered_function}"
        )))
    }

    /// `Wrap`: validate the verifier-selected head-membership child and use
    /// the exact WD application layer to construct membership in the
    /// instantiated declared return carrier. No function search or return-set
    /// inference is repeated here.
    pub(super) fn construct_lean_function_application_return_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionApplicationReturnMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-application return evidence changed its target".into());
        }
        let [head_membership_result] = subgoals else {
            return Err(
                "function-application return evidence requires one head-membership child".into(),
            );
        };
        let head_membership_result = head_membership_result
            .factual_success()
            .ok_or_else(|| "function head-membership child is not factual".to_string())?;
        if head_membership_result.fact().to_string()
            != evidence.expected_head_membership.to_string()
            || !head_membership_result.store.infers.is_empty()
        {
            return Err(
                "function head-membership child changed its proposition or published effects"
                    .into(),
            );
        }
        let Some(_head_membership_proof) =
            self.construct_lean_proof_from_direct_fact_result(head_membership_result)?
        else {
            return Ok(None);
        };

        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-application return evidence targets a non-membership".into());
        };
        let Obj::FnObj(application) = &target_membership.element else {
            return Err("function-application return evidence targets a non-application".into());
        };
        let Fact::AtomicFact(AtomicFact::InFact(head_membership)) =
            &evidence.expected_head_membership
        else {
            return Err("function head contract is not a membership fact".into());
        };
        if !matches!(&head_membership.set, Obj::FnSet(_)) {
            return Err("function head contract retained a non-function carrier".into());
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        if !objs_equal_with_nested_binder_alpha_equivalence(
            &head_membership.element,
            &application_head,
        ) || !objs_equal_with_nested_binder_alpha_equivalence(
            &target_membership.set,
            &evidence.typed_return_set,
        ) {
            return Err("function-application return evidence changed its head or carrier".into());
        }

        let rendered_application = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_return_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_target = format!("Litex.In {rendered_application} {rendered_return_set}");
        if rendered_target != expected_target {
            return Err("function-application return evidence changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_return_set} {rendered_application}"
        )))
    }

    pub(super) fn construct_lean_combined_fact_proof_from_result(
        &mut self,
        target: &Fact,
        combined: &SuccessCombinedFactProofResult,
    ) -> Result<Option<String>, String> {
        if let Some(primary) = combined.primary.as_ref() {
            if primary.fact().to_string() != target.to_string() {
                return Err("combined primary proof changed its target".into());
            }
            for (index, step) in combined.steps.iter().enumerate() {
                let Some(factual) = step.factual_success() else {
                    return Err(format!("combined proof step {index} is not factual"));
                };
                if self
                    .construct_lean_proof_from_direct_fact_result(factual)?
                    .is_none()
                {
                    return Ok(None);
                }
            }
            return self.construct_lean_proof_from_shared_verify_fact_result(primary);
        }

        let components = conjunction_components(target)?;
        if components.len() != combined.steps.len() {
            return Err("combined fact proof changed its component arity".into());
        }
        let mut proofs = Vec::with_capacity(components.len());
        for (component, step) in components.iter().zip(combined.steps.iter()) {
            let factual = step
                .factual_success()
                .ok_or_else(|| "combined proof child is not factual".to_string())?;
            if factual.fact().to_string() != component.to_string() {
                return Err("combined proof child changed its component".into());
            }
            let proof = self.construct_lean_proof_from_direct_fact_result(factual)?;
            let Some(proof) = proof else {
                return Ok(None);
            };
            proofs.push(proof);
        }
        Ok(Some(right_associated_conjunction_proof(&proofs)?))
    }

    pub(super) fn construct_lean_proof_from_shared_verify_fact_result(
        &mut self,
        verification: &SuccessVerifyFactResult,
    ) -> Result<Option<String>, String> {
        let source_fact = verification.fact();
        match verification.proof() {
            SuccessFactProofResult::StoredFactCitation(citation) => {
                self.construct_lean_stored_fact_citation_proof_from_result(&source_fact, citation)
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => self
                .construct_lean_checked_function_definition_reduction_from_result(
                    &source_fact,
                    &result.verification,
                )
                .map(Some),
            SuccessFactProofResult::Strategy(_)
            | SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => Ok(None),
            SuccessFactProofResult::BuiltinRule(builtin)
            | SuccessFactProofResult::BuiltinStrategy(builtin) => {
                if let Some(BuiltinRuleEvidence::ListSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_list_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RefinedNumericMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_refined_numeric_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::NotEqualSymmetry)
                ) {
                    return self.construct_lean_not_equal_symmetry_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) =
                        builtin.evidence.typed()
                    else {
                        unreachable!("disjunction evidence checked above")
                    };
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_builder_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_application_return_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_local_builtin_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Arithmetic(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_arithmetic_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_real_arithmetic_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegerMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integer_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::NaturalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_natural_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RationalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_rational_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Set(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_set_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::KnownEqualityPath(evidence)) =
                    builtin.evidence.typed()
                {
                    return Ok(Some(self.construct_lean_known_equality_path_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    )?));
                }
                if let Some(BuiltinRuleEvidence::SetRelationDuality(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_relation_duality_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    if !builtin.subgoals.is_empty() {
                        return Err(
                            "shared registered reflexive-predicate proof retained child Results"
                                .into(),
                        );
                    }
                    return Ok(Some(
                        construct_lean_registered_reflexive_predicate_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    ));
                }
                if let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_symmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_antisymmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_complex_algebraic_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(evidence) = builtin.evidence.typed() {
                    if let Some(limitation) = direct_builtin_rule_compiler_limitation(evidence) {
                        return Err(limitation.to_string());
                    }
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match builtin.evidence.typed() {
                    Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "shared object-reflexivity evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if evidence.expected_target.to_string() != source_fact.to_string()
                            || obj_equality_key(&equality.left) != obj_equality_key(&equality.right)
                        {
                            return Err(
                                "shared object-reflexivity evidence changed its target".into()
                            );
                        }
                        Ok(Some(format!(
                            "Litex.Same.refl {}",
                            render_obj(&equality.left, &self.environment_stack)?
                        )))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared rational-normalization evidence changed its target".into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "shared rational-normalization retained unequal normal forms"
                                    .into(),
                            );
                        }
                        Ok(Some(
                            "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                                .into(),
                        ))
                    }
                    Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) => {
                        self.construct_lean_complex_algebraic_normalization_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        validate_closed_numeric_comparison_builtin_rule_evidence(
                            &source_fact,
                            evidence,
                        )?;
                        Ok(Some(render_closed_numeric_comparison_fact(
                            &source_fact,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::OrderReflexivity(evidence)) => Ok(Some(
                        construct_lean_order_reflexivity_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence)) => self
                        .construct_lean_runtime_resolved_numeric_comparison_from_assignment_result(
                            &source_fact,
                            evidence,
                        )
                        .map(Some),
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared closed-numeric-membership changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericNonmembership(evidence)) => self
                        .construct_lean_closed_numeric_nonmembership_from_result(
                            &source_fact,
                            evidence,
                        ),
                    Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) => Ok(Some(
                        self.construct_lean_standard_set_nonempty_from_result(
                            &source_fact,
                            evidence,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::NativeConstantMembership(rule)) => Ok(Some(
                        self.construct_lean_native_constant_membership_from_result(
                            &source_fact,
                            *rule,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::StandardSetSubset) => Ok(Some(
                        self.construct_lean_standard_set_subset_from_result(&source_fact)?,
                    )),
                    Some(BuiltinRuleEvidence::PrimeU64Reflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            true,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::CoprimeNaturalReflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            false,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::FiniteSet(rule)) => Ok(Some(
                        self.construct_lean_finite_set_from_result(&source_fact, *rule)?,
                    )),
                    Some(BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule)) => Ok(
                        Some(self.construct_lean_complex_membership_closure_from_result(
                            &source_fact,
                            *rule,
                        )?),
                    ),
                    Some(BuiltinRuleEvidence::TupleLiteralShape) => Ok(Some(
                        self.construct_lean_tuple_literal_shape_from_result(&source_fact)?,
                    )),
                    None => Ok(None),
                    Some(evidence) => unreachable!(
                        "typed shared builtin evidence must be handled before the terminal direct compiler dispatch: {evidence:?}"
                    ),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::KnownForallInstantiation(instantiation) => self
                .construct_lean_known_forall_instantiation_from_result(&source_fact, instantiation),
            SuccessFactProofResult::Transform(transformation) => self
                .construct_lean_single_fact_transformation_from_result(
                    &source_fact,
                    transformation,
                ),
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            SuccessFactProofResult::ForallProof(_) => Ok(None),
        }
    }

    /// `Wrap`: compile the exact reordered predicate child retained by the
    /// verifier, then replay the registered permutation theorem until the
    /// requested target ordering is reached. Repeating the theorem matters for
    /// non-involutive permutations: the Runtime checks `P(target)`, while a
    /// theorem registered as `source -> P(source)` may need more than one
    /// application to return from that premise to `target`.
    pub(super) fn construct_lean_registered_symmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredSymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered symmetric-predicate evidence changed its target".into());
        }
        let Fact::AtomicFact(target_atomic @ AtomicFact::NormalAtomicFact(target_predicate)) =
            target
        else {
            return Err(
                "registered symmetric-predicate evidence targets a non-user predicate".into(),
            );
        };
        if target_predicate.predicate.to_string() != evidence.predicate_name
            || target_predicate.body.len() < 2
        {
            return Err(
                "registered symmetric-predicate evidence changed its predicate or arity".into(),
            );
        }
        let expected_alternate_from_gather: Fact = target_atomic
            .symmetric_reordered_args(&evidence.gather)
            .ok_or_else(|| {
                "registered symmetric-predicate evidence retained an invalid permutation"
                    .to_string()
            })?
            .into();
        if expected_alternate_from_gather.to_string() != evidence.expected_alternate.to_string() {
            return Err(
                "registered symmetric-predicate evidence changed its reordered premise".into(),
            );
        }
        let [alternate_result] = subgoals else {
            return Err(
                "registered symmetric-predicate proof requires exactly one child Result".into(),
            );
        };
        let alternate_result = alternate_result
            .factual_success()
            .ok_or_else(|| "registered symmetric-predicate child is not factual".to_string())?;
        if alternate_result.fact().to_string() != evidence.expected_alternate.to_string()
            || alternate_result.store.fact.to_string() != evidence.expected_alternate.to_string()
            || !alternate_result.store.infers.is_empty()
        {
            return Err(
                "registered symmetric-predicate child changed its fact or published effects".into(),
            );
        }

        let bindings = self
            .environment_stack
            .registered_symmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .ok_or_else(|| {
                format!(
                    "registered symmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let mut selected_binding = None;
        for binding in bindings.iter().rev() {
            let binding_gather = registered_symmetric_predicate_gather(
                &binding.forall_fact,
                &evidence.predicate_name,
            )?;
            if binding_gather == evidence.gather {
                selected_binding = Some(binding.clone());
                break;
            }
        }
        let binding = selected_binding.ok_or_else(|| {
            format!(
                "registered symmetry theorem for `{}` does not own permutation {:?}",
                evidence.predicate_name, evidence.gather
            )
        })?;

        render_fact(target, &self.environment_stack)?;
        let Some(mut proof) =
            self.construct_lean_proof_from_direct_fact_result(alternate_result)?
        else {
            return Ok(None);
        };
        let mut current = evidence.expected_alternate.clone();
        let mut visited = HashSet::new();
        visited.insert(current.to_string());
        loop {
            let (next, parameter_arguments) =
                instantiate_registered_symmetric_predicate_transition(
                    &binding.forall_fact,
                    &evidence.predicate_name,
                    &current,
                )?;
            let mut theorem_application = binding.theorem_name.clone();
            for argument in parameter_arguments {
                theorem_application.push(' ');
                theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
            }
            theorem_application.push_str(&format!(" ({proof})"));
            proof = theorem_application;
            if next.to_string() == target.to_string() {
                return Ok(Some(proof));
            }
            if !visited.insert(next.to_string()) {
                return Err(
                    "registered symmetric-predicate permutation cycled without reaching its target"
                        .into(),
                );
            }
            current = next;
        }
    }

    /// `Combine`: compile the two ordered predicate-premise children and apply
    /// the exact antisymmetry theorem currently visible in the compiler
    /// environment created by an earlier registration Result.
    pub(super) fn construct_lean_registered_antisymmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredAntisymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered antisymmetric-predicate evidence changed its target".into());
        }
        let binding = self
            .environment_stack
            .registered_antisymmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "registered antisymmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let (parameter_arguments, expected_premises) =
            instantiate_registered_antisymmetric_predicate_application(
                &binding.forall_fact,
                &evidence.predicate_name,
                target,
            )?;
        if subgoals.len() != expected_premises.len() {
            return Err(
                "registered antisymmetric-predicate proof lost an ordered child Result".into(),
            );
        }
        let mut premise_proofs = Vec::with_capacity(subgoals.len());
        for (index, (subgoal, expected)) in
            subgoals.iter().zip(expected_premises.iter()).enumerate()
        {
            let subgoal = subgoal.factual_success().ok_or_else(|| {
                format!("registered antisymmetric-predicate child {index} is not factual")
            })?;
            if subgoal.fact().to_string() != expected.to_string()
                || subgoal.store.fact.to_string() != expected.to_string()
                || !subgoal.store.infers.is_empty()
            {
                return Err(format!(
                    "registered antisymmetric-predicate child {index} changed its fact or published effects"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(subgoal)? else {
                return Ok(None);
            };
            premise_proofs.push(proof);
        }

        render_fact(target, &self.environment_stack)?;
        let mut theorem_application = binding.theorem_name;
        for argument in parameter_arguments {
            theorem_application.push(' ');
            theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
        }
        for proof in premise_proofs {
            theorem_application.push_str(&format!(" ({proof})"));
        }
        Ok(Some(theorem_application))
    }
}
