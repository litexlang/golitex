//! Real-analysis builtin theorem contracts and application.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_real_analysis_builtin_theorem_application(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let Some(compiled) =
            self.construct_real_analysis_builtin_theorem_application_proof(result, false)?
        else {
            return Ok(false);
        };
        if !compiled.local_prerequisite_lines.is_empty() {
            return Err(
                "top-level real-analysis theorem application retained local prerequisite lines"
                    .into(),
            );
        }
        let conclusion = compiled.conclusion;
        let conclusion_fact_id = conclusion.retained_fact_id.ok_or_else(|| {
            "real-analysis builtin theorem conclusion has no frozen FactId".to_string()
        })?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            conclusion.proposition, conclusion.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.next_fact_name_index += 1;
        self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
            &result.common.infers,
            &[(conclusion_fact_id, conclusion.fact)],
            &format!(
                "real-analysis builtin theorem `{}` outer inference",
                result.statement.name
            ),
        )?;
        Ok(true)
    }

    pub(in super::super) fn construct_local_real_analysis_builtin_theorem_application_proof(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<Option<CompiledRealAnalysisTheoremApplicationProofBody>, String> {
        self.construct_real_analysis_builtin_theorem_application_proof(result, true)
    }

    /// Construct one proof application from the verifier-owned builtin theorem
    /// Result. Requirement Results are replayed in their retained order. A
    /// direct `ForallProof` is published as a theorem at top level or as a
    /// local `have` inside a named theorem; both paths preserve the same exact
    /// FactId and generated Lean name.
    fn construct_real_analysis_builtin_theorem_application_proof(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
        requirements_are_local: bool,
    ) -> Result<Option<CompiledRealAnalysisTheoremApplicationProofBody>, String> {
        let verification = result
            .verification
            .as_ref()
            .ok_or_else(|| "real-analysis builtin theorem lost its verification".to_string())?;
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &verification.source
        else {
            return Ok(None);
        };
        if !matches!(
            source.theorem_id,
            BuiltinTheoremId::RealLeastUpperBoundExists
                | BuiltinTheoremId::RealMemberLeLeastUpperBound
                | BuiltinTheoremId::RealLeastUpperBoundLeUpperBound
                | BuiltinTheoremId::RealGreatestLowerBoundExists
                | BuiltinTheoremId::RealGreatestLowerBoundLeMember
                | BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound
                | BuiltinTheoremId::RealArchimedeanNaturalUpperBound
                | BuiltinTheoremId::RationalBetweenReals
        ) {
            return Ok(None);
        }
        if verification.theorem != source.theorem_id.as_str()
            || verification.theorem != result.statement.name.to_string()
            || verification.arguments.len() != result.statement.args.len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args.iter())
                .any(|(retained, statement)| !same_compiler_object(retained, statement))
        {
            return Err(
                "real-analysis builtin theorem Result changed its identity or argument order"
                    .into(),
            );
        }
        let expected_roles = builtin_theorem_requirement_roles(source.theorem_id);
        if source.requirement_roles != expected_roles
            || source.requirement_facts.len() != expected_roles.len()
            || source.requirement_checks.len() != expected_roles.len()
            || source.provenance.is_some()
        {
            return Err(
                "real-analysis builtin theorem Result changed its typed requirement schema".into(),
            );
        }
        let conclusion_well_definedness =
            source.conclusion_well_definedness.as_ref().ok_or_else(|| {
                "real-analysis builtin theorem lost dedicated conclusion WD evidence".to_string()
            })?;
        let [conclusion] = verification.direct_conclusions.as_slice() else {
            return Err("real-analysis builtin theorem must retain one direct conclusion".into());
        };
        validate_real_analysis_builtin_contract(
            source.theorem_id,
            &verification.arguments,
            &source.requirement_facts,
            conclusion,
        )?;

        // Arguments such as `a(n) + 1` are checked inside the theorem's
        // requirement Results, not by the enclosing proof statement. Merge
        // those exact occurrence indexes with the conclusion certificate for
        // the complete application replay; never fall back to a structural
        // search in the ambient theorem context.
        let mut application_well_definedness =
            StmtResultWellDefinednessToLeanCompilationContext::default();
        let mut application_well_definedness_roots = Vec::new();
        for (index, check) in source.requirement_checks.iter().enumerate() {
            let check = check.factual_success().ok_or_else(|| {
                format!(
                    "real-analysis builtin requirement {} is not factual",
                    index + 1
                )
            })?;
            if let Some(recursive) = check.well_definedness.recursive.as_deref() {
                application_well_definedness.merge_from(
                    &self.collect_well_definedness_to_lean_compilation_context(
                        &check.well_definedness,
                    )?,
                )?;
                application_well_definedness_roots.push(recursive);
            }
        }
        if let Some(recursive) = conclusion_well_definedness.recursive.as_deref() {
            application_well_definedness.merge_from(
                &self.collect_well_definedness_to_lean_compilation_context(
                    conclusion_well_definedness,
                )?,
            )?;
            application_well_definedness_roots.push(recursive);
        }
        let application_well_definedness = self.compile_precollected_well_definedness_context(
            application_well_definedness,
            &application_well_definedness_roots,
        )?;
        let previous_well_definedness = self
            .environment_stack
            .well_definedness
            .replace(application_well_definedness);
        let compilation = (|| {
            // Rational density is a theorem about native real endpoints.  Lower
            // each verifier-checked endpoint once to its exact ℝ observation and
            // use that same term for the rule arguments, memberships, order
            // premise, and existential conclusion.
            let rational_density_real_arguments =
                if matches!(source.theorem_id, BuiltinTheoremId::RationalBetweenReals) {
                    Some(
                        verification
                            .arguments
                            .iter()
                            .map(|argument| {
                                render_real_target_object_representation(
                                    &LeanTargetObjectRepresentation::lower(argument)?,
                                    &self.environment_stack,
                                )
                            })
                            .collect::<Result<Vec<_>, String>>()?,
                    )
                } else {
                    None
                };

            let mut requirement_proofs = Vec::with_capacity(source.requirement_checks.len());
            let mut local_prerequisite_lines = Vec::new();
            for (index, ((requirement, role), check)) in source
                .requirement_facts
                .iter()
                .zip(source.requirement_roles.iter())
                .zip(source.requirement_checks.iter())
                .enumerate()
            {
                let check = check.factual_success().ok_or_else(|| {
                    format!(
                        "real-analysis builtin requirement {} is not factual",
                        index + 1
                    )
                })?;
                validate_scoped_fact_check_result(
                    check,
                    requirement,
                    "real-analysis builtin requirement child",
                )?;
                self.install_atomic_fact_well_definedness_store_results(check)
                    .map_err(|error| {
                        format!(
                            "real-analysis builtin requirement {} WD installation: {error}",
                            index + 1
                        )
                    })?;
                let proof = if matches!(check.proof(), SuccessFactProofResult::ForallProof(_)) {
                    let theorem_name = format!("__fact{}", self.next_fact_name_index);
                    let fact_index = self.next_fact_name_index;
                    if requirements_are_local {
                        let Some(lines) =
                            self.compile_direct_forall_fact_result_as_local_proof_steps(check)?
                        else {
                            return Err(format!(
                            "real-analysis builtin requirement {} retained an unsupported ForallProof",
                            index + 1
                        ));
                        };
                        if lines.len() != 1 || self.next_fact_name_index != fact_index + 1 {
                            return Err(format!(
                            "real-analysis builtin requirement {} compiled an unexpected number of local forall projections",
                            index + 1
                        ));
                        }
                        local_prerequisite_lines.extend(lines);
                    } else {
                        let declaration_count = self.declarations.len();
                        if !self.compile_direct_forall_fact_result(check)? {
                            return Err(format!(
                            "real-analysis builtin requirement {} retained an unsupported ForallProof",
                            index + 1
                        ));
                        }
                        if self.declarations.len() != declaration_count + 1
                            || self.next_fact_name_index != fact_index + 1
                        {
                            return Err(format!(
                            "real-analysis builtin requirement {} compiled an unexpected number of forall projections",
                            index + 1
                        ));
                        }
                    }
                    theorem_name
                } else {
                    self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                        check,
                    )?
                    .ok_or_else(|| {
                        format!(
                        "real-analysis builtin requirement {} has no direct typed proof consumer",
                        index + 1
                    )
                    })?
                };
                let proof = if matches!(
                    role,
                    BuiltinTheoremRequirementRole::CandidateBelongsToReals
                ) {
                    let (numeric_object, target_set) = membership_parts(requirement)?;
                    if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
                        return Err(format!(
                        "real-analysis builtin requirement {} changed its real-membership target",
                        index + 1
                    ));
                    }
                    render_numeric_operand_membership(
                        numeric_object,
                        &proof,
                        &self.environment_stack,
                    )
                } else if matches!(
                    role,
                    BuiltinTheoremRequirementRole::SuppliedUpperBoundBelongsToReals
                        | BuiltinTheoremRequirementRole::SuppliedLowerBoundBelongsToReals
                        | BuiltinTheoremRequirementRole::ArgumentBelongsToReals
                ) {
                    let (numeric_object, target_set) = membership_parts(requirement)?;
                    if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
                        return Err(format!(
                        "real-analysis builtin requirement {} changed its real-membership target",
                        index + 1
                    ));
                    }
                    let exact_real = render_real_target_object_representation(
                        &LeanTargetObjectRepresentation::lower(numeric_object)?,
                        &self.environment_stack,
                    )?;
                    format!("Litex.In.own Litex.R {exact_real}")
                } else if let Some(real_arguments) = rational_density_real_arguments.as_ref() {
                    match role {
                        BuiltinTheoremRequirementRole::LeftArgumentBelongsToReals => {
                            format!("Litex.In.own Litex.R {}", real_arguments[0])
                        }
                        BuiltinTheoremRequirementRole::RightArgumentBelongsToReals => {
                            format!("Litex.In.own Litex.R {}", real_arguments[1])
                        }
                        BuiltinTheoremRequirementRole::RealArgumentsStrictlyOrdered => {
                            if let SuccessFactProofResult::BuiltinRule(builtin) = check.proof() {
                                if let Some(BuiltinRuleEvidence::ClosedNumericComparison(
                                    evidence,
                                )) = builtin.evidence.typed()
                                {
                                    validate_closed_numeric_comparison_builtin_rule_evidence(
                                        requirement,
                                        evidence,
                                    )?;
                                    format!(
                                    "(Litex.OrderBridge.ltOfComplexReals (show {} < {} by norm_num) : Litex.Lt (({}) : ℂ) (({}) : ℂ))",
                                    real_arguments[0],
                                    real_arguments[1],
                                    real_arguments[0],
                                    real_arguments[1],
                                )
                                } else {
                                    proof
                                }
                            } else {
                                proof
                            }
                        }
                        _ => proof,
                    }
                } else {
                    proof
                };
                requirement_proofs.push(format!("({proof})"));
            }

            let rendered_arguments = verification
                .arguments
                .iter()
                .enumerate()
                .map(|(argument_index, argument)| {
                    if matches!(source.theorem_id, BuiltinTheoremId::RationalBetweenReals) {
                        Ok(rational_density_real_arguments
                            .as_ref()
                            .expect("rational density real arguments were installed")
                            [argument_index]
                            .clone())
                    } else if matches!(
                        source.theorem_id,
                        BuiltinTheoremId::RealArchimedeanNaturalUpperBound
                    ) {
                        render_obj(argument, &self.environment_stack)
                    } else if matches!(
                        (source.theorem_id, argument_index),
                        (BuiltinTheoremId::RealLeastUpperBoundExists, 1)
                            | (BuiltinTheoremId::RealLeastUpperBoundLeUpperBound, 2)
                            | (BuiltinTheoremId::RealGreatestLowerBoundExists, 1)
                            | (BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound, 2)
                    ) {
                        render_real_target_object_representation(
                            &LeanTargetObjectRepresentation::lower(argument)?,
                            &self.environment_stack,
                        )
                    } else if matches!(
                        (source.theorem_id, argument_index),
                        (BuiltinTheoremId::RealMemberLeLeastUpperBound, 1)
                            | (BuiltinTheoremId::RealLeastUpperBoundLeUpperBound, 1)
                            | (BuiltinTheoremId::RealGreatestLowerBoundLeMember, 1)
                            | (BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound, 1)
                    ) {
                        render_numeric_obj(argument, &self.environment_stack)
                    } else if matches!(
                        (source.theorem_id, argument_index),
                        (BuiltinTheoremId::RealMemberLeLeastUpperBound, 2)
                            | (BuiltinTheoremId::RealGreatestLowerBoundLeMember, 2)
                    ) {
                        // The membership premise is evidence about this exact
                        // source object.  The real observer is supplied
                        // separately and applied by the Lean rule after selecting
                        // the set-carrier representative.
                        render_obj(argument, &self.environment_stack)
                    } else {
                        render_obj(argument, &self.environment_stack)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let rule_name = match source.theorem_id {
                BuiltinTheoremId::RealLeastUpperBoundExists => {
                    "Litex.Rules.realLeastUpperBoundExists"
                }
                BuiltinTheoremId::RealMemberLeLeastUpperBound => {
                    "Litex.Rules.realMemberLeLeastUpperBound"
                }
                BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => {
                    "Litex.Rules.realLeastUpperBoundLeUpperBound"
                }
                BuiltinTheoremId::RealGreatestLowerBoundExists => {
                    "Litex.Rules.realGreatestLowerBoundExists"
                }
                BuiltinTheoremId::RealGreatestLowerBoundLeMember => {
                    "Litex.Rules.realGreatestLowerBoundLeMember"
                }
                BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound => {
                    "Litex.Rules.realLowerBoundLeGreatestLowerBound"
                }
                BuiltinTheoremId::RealArchimedeanNaturalUpperBound => {
                    "Litex.Rules.realArchimedeanNaturalUpperBound"
                }
                BuiltinTheoremId::RationalBetweenReals => "Litex.Rules.rationalBetweenReals",
                _ => unreachable!("typed real-analysis theorem set was checked above"),
            };
            let mut representation_arguments = Vec::new();
            if matches!(
                source.theorem_id,
                BuiltinTheoremId::RealArchimedeanNaturalUpperBound
            ) {
                representation_arguments.push(render_numeric_obj(
                    &verification.arguments[0],
                    &self.environment_stack,
                )?);
                representation_arguments.push("(by norm_num)".to_string());
            }
            if matches!(
                source.theorem_id,
                BuiltinTheoremId::RealLeastUpperBoundExists
                    | BuiltinTheoremId::RealMemberLeLeastUpperBound
                    | BuiltinTheoremId::RealLeastUpperBoundLeUpperBound
                    | BuiltinTheoremId::RealGreatestLowerBoundExists
                    | BuiltinTheoremId::RealGreatestLowerBoundLeMember
                    | BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound
            ) {
                let set = LeanTargetObjectRepresentation::lower(&verification.arguments[0])?;
                let observer = render_real_set_observer(&set, &self.environment_stack, "__member")?;
                representation_arguments.push(format!("(fun __member => {observer})"));
                representation_arguments.push("(by rfl)".to_string());
                if matches!(
                    source.theorem_id,
                    BuiltinTheoremId::RealLeastUpperBoundExists
                        | BuiltinTheoremId::RealGreatestLowerBoundExists
                ) {
                    let same =
                        render_real_set_observer_same(&set, &self.environment_stack, "__member")?;
                    representation_arguments.push(format!("(fun __member => {same})"));
                }
            }
            let mut proof = format!(
                "{rule_name} {} {} {}",
                rendered_arguments.join(" "),
                representation_arguments.join(" "),
                requirement_proofs.join(" ")
            );
            if matches!(
                source.theorem_id,
                BuiltinTheoremId::RealMemberLeLeastUpperBound
                    | BuiltinTheoremId::RealGreatestLowerBoundLeMember
            ) {
                proof = format!("(by simpa using ({proof}))");
            }
            let proposition = self.render_fact_using_well_definedness_result(
                conclusion_well_definedness,
                conclusion,
            )?;

            let [outer_store] = result.common.infers.store_fact_outputs.as_slice() else {
                return Err(
                    "real-analysis builtin theorem must retain one outer conclusion store".into(),
                );
            };
            let conclusion_fact_id = outer_store.fact_id.ok_or_else(|| {
                "real-analysis builtin theorem conclusion has no frozen FactId".to_string()
            })?;
            if outer_store.itself_and_why_itself_is_stored.0.to_string() != conclusion.to_string()
                || outer_store.inferred_facts.len() != outer_store.inferred_fact_ids.len()
            {
                return Err("real-analysis builtin theorem changed its publication effects".into());
            }
            Ok(Some(CompiledRealAnalysisTheoremApplicationProofBody {
                local_prerequisite_lines,
                conclusion: CompiledTheoremApplicationConclusionProofBody {
                    retained_fact_id: Some(conclusion_fact_id),
                    fact: conclusion.clone(),
                    proposition,
                    proof_expression: proof,
                },
            }))
        })();
        self.environment_stack.well_definedness = previous_well_definedness;
        compilation
    }
}

fn same_compiler_object(left: &Obj, right: &Obj) -> bool {
    obj_equality_key(left) == obj_equality_key(right)
}

fn fact_is_subset_of(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::SubsetFact(subset))
            if same_compiler_object(&subset.left, left)
                && same_compiler_object(&subset.right, right)
    )
}

fn fact_is_nonempty(set: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty))
            if same_compiler_object(&nonempty.set, set)
    )
}

fn fact_is_membership(element: &Obj, set: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::InFact(membership))
            if same_compiler_object(&membership.element, element)
                && same_compiler_object(&membership.set, set)
    )
}

fn fact_is_less(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::LessFact(less))
            if same_compiler_object(&less.left, left)
                && same_compiler_object(&less.right, right)
    )
}

fn fact_is_less_equal(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::LessEqualFact(less_equal))
            if same_compiler_object(&less_equal.left, left)
                && same_compiler_object(&less_equal.right, right)
    )
}

fn atomic_is_real_lub_certificate(set: &Obj, candidate: &Obj, fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NormalAtomicFact(certificate)
            if certificate.predicate.to_string() == IS_REAL_LEAST_UPPER_BOUND
                && certificate.body.len() == 2
                && same_compiler_object(&certificate.body[0], set)
                && same_compiler_object(&certificate.body[1], candidate)
    )
}

fn fact_is_real_lub_certificate(set: &Obj, candidate: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(atomic)
            if atomic_is_real_lub_certificate(set, candidate, atomic)
    )
}

fn atomic_is_real_glb_certificate(set: &Obj, candidate: &Obj, fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NormalAtomicFact(certificate)
            if certificate.predicate.to_string() == IS_REAL_GREATEST_LOWER_BOUND
                && certificate.body.len() == 2
                && same_compiler_object(&certificate.body[0], set)
                && same_compiler_object(&certificate.body[1], candidate)
    )
}

fn fact_is_real_glb_certificate(set: &Obj, candidate: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(atomic)
            if atomic_is_real_glb_certificate(set, candidate, atomic)
    )
}

fn fact_is_real_upper_bound_forall(set: &Obj, upper_bound: &Obj, fact: &Fact) -> bool {
    let Fact::ForallFact(forall) = fact else {
        return false;
    };
    let [group] = forall.typed_parameters.groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    if !same_compiler_object(parameter_set, set) {
        return false;
    }
    let member = obj_for_bound_param_in_scope(binding);
    if !forall.dom_facts.is_empty() {
        return false;
    }
    let [conclusion] = forall.then_facts.as_slice() else {
        return false;
    };
    let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = conclusion else {
        return false;
    };
    matches!(
        conclusion,
        AtomicFact::LessEqualFact(less_equal)
            if same_compiler_object(&less_equal.left, &member)
                && same_compiler_object(&less_equal.right, upper_bound)
    )
}

fn fact_is_real_lower_bound_forall(set: &Obj, lower_bound: &Obj, fact: &Fact) -> bool {
    let Fact::ForallFact(forall) = fact else {
        return false;
    };
    let [group] = forall.typed_parameters.groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    if !same_compiler_object(parameter_set, set) || !forall.dom_facts.is_empty() {
        return false;
    }
    let [conclusion] = forall.then_facts.as_slice() else {
        return false;
    };
    let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = conclusion else {
        return false;
    };
    let member = obj_for_bound_param_in_scope(binding);
    matches!(
        conclusion,
        AtomicFact::LessEqualFact(less_equal)
            if same_compiler_object(&less_equal.left, lower_bound)
                && same_compiler_object(&less_equal.right, &member)
    )
}

fn validate_real_lub_existential(set: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let real: Obj = StandardSet::R.into();
    if !same_compiler_object(parameter_set, &real) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AtomicFact(body) = body else {
        return false;
    };
    atomic_is_real_lub_certificate(set, &obj_for_bound_param_in_scope(binding), body)
}

fn validate_real_glb_existential(set: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let real: Obj = StandardSet::R.into();
    if !same_compiler_object(parameter_set, &real) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AtomicFact(body) = body else {
        return false;
    };
    atomic_is_real_glb_certificate(set, &obj_for_bound_param_in_scope(binding), body)
}

fn validate_real_archimedean_existential(value: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let positive_naturals: Obj = StandardSet::NPos.into();
    if !same_compiler_object(parameter_set, &positive_naturals) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(less)) = body else {
        return false;
    };
    same_compiler_object(&less.left, value)
        && same_compiler_object(&less.right, &obj_for_bound_param_in_scope(binding))
}

fn validate_rational_between_existential(left: &Obj, right: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let rationals: Obj = StandardSet::Q.into();
    if !same_compiler_object(parameter_set, &rationals) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AndFact(body) = body else {
        return false;
    };
    let [left_less, right_less] = body.facts.as_slice() else {
        return false;
    };
    let rational = obj_for_bound_param_in_scope(binding);
    matches!(
        left_less,
        AtomicFact::LessFact(less)
            if same_compiler_object(&less.left, left)
                && same_compiler_object(&less.right, &rational)
    ) && matches!(
        right_less,
        AtomicFact::LessFact(less)
            if same_compiler_object(&less.left, &rational)
                && same_compiler_object(&less.right, right)
    )
}

fn validate_real_analysis_builtin_contract(
    theorem_id: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &Fact,
) -> Result<(), String> {
    let real: Obj = StandardSet::R.into();
    let valid = match theorem_id {
        BuiltinTheoremId::RealLeastUpperBoundExists => {
            let ([set, upper_bound], [subset, nonempty, upper_real, upper_forall]) =
                (arguments, requirements)
            else {
                return Err("real LUB existence Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_nonempty(set, nonempty)
                && fact_is_membership(upper_bound, &real, upper_real)
                && fact_is_real_upper_bound_forall(set, upper_bound, upper_forall)
                && validate_real_lub_existential(set, conclusion)
        }
        BuiltinTheoremId::RealMemberLeLeastUpperBound => {
            let ([set, candidate, member], [subset, candidate_real, certificate, membership]) =
                (arguments, requirements)
            else {
                return Err("real LUB member projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_lub_certificate(set, candidate, certificate)
                && fact_is_membership(member, set, membership)
                && fact_is_less_equal(member, candidate, conclusion)
        }
        BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => {
            let (
                [set, candidate, upper_bound],
                [subset, candidate_real, certificate, upper_real, upper_forall],
            ) = (arguments, requirements)
            else {
                return Err("real LUB upper-bound projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_lub_certificate(set, candidate, certificate)
                && fact_is_membership(upper_bound, &real, upper_real)
                && fact_is_real_upper_bound_forall(set, upper_bound, upper_forall)
                && fact_is_less_equal(candidate, upper_bound, conclusion)
        }
        BuiltinTheoremId::RealGreatestLowerBoundExists => {
            let ([set, lower_bound], [subset, nonempty, lower_real, lower_forall]) =
                (arguments, requirements)
            else {
                return Err("real GLB existence Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_nonempty(set, nonempty)
                && fact_is_membership(lower_bound, &real, lower_real)
                && fact_is_real_lower_bound_forall(set, lower_bound, lower_forall)
                && validate_real_glb_existential(set, conclusion)
        }
        BuiltinTheoremId::RealGreatestLowerBoundLeMember => {
            let ([set, candidate, member], [subset, candidate_real, certificate, membership]) =
                (arguments, requirements)
            else {
                return Err("real GLB member projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_glb_certificate(set, candidate, certificate)
                && fact_is_membership(member, set, membership)
                && fact_is_less_equal(candidate, member, conclusion)
        }
        BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound => {
            let (
                [set, candidate, lower_bound],
                [subset, candidate_real, certificate, lower_real, lower_forall],
            ) = (arguments, requirements)
            else {
                return Err("real GLB lower-bound projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_glb_certificate(set, candidate, certificate)
                && fact_is_membership(lower_bound, &real, lower_real)
                && fact_is_real_lower_bound_forall(set, lower_bound, lower_forall)
                && fact_is_less_equal(lower_bound, candidate, conclusion)
        }
        BuiltinTheoremId::RealArchimedeanNaturalUpperBound => {
            let ([value], [value_real]) = (arguments, requirements) else {
                return Err("real Archimedean Result changed its arity".into());
            };
            fact_is_membership(value, &real, value_real)
                && validate_real_archimedean_existential(value, conclusion)
        }
        BuiltinTheoremId::RationalBetweenReals => {
            let ([left, right], [left_real, right_real, ordered]) = (arguments, requirements)
            else {
                return Err("rational density Result changed its arity".into());
            };
            fact_is_membership(left, &real, left_real)
                && fact_is_membership(right, &real, right_real)
                && fact_is_less(left, right, ordered)
                && validate_rational_between_existential(left, right, conclusion)
        }
        _ => return Err("non-analysis theorem reached real-analysis validator".into()),
    };
    if valid {
        Ok(())
    } else {
        Err("real-analysis builtin theorem changed its structural fact contract".into())
    }
}

pub(super) fn builtin_theorem_requirement_roles(
    theorem_id: BuiltinTheoremId,
) -> Vec<BuiltinTheoremRequirementRole> {
    use BuiltinTheoremRequirementRole as Role;
    match theorem_id {
        BuiltinTheoremId::SubsetOfFiniteSetIsFinite => vec![
            Role::FirstArgumentIsSet,
            Role::SecondArgumentIsFiniteSet,
            Role::FirstArgumentSubsetOfSecond,
        ],
        BuiltinTheoremId::FiniteSetHasBijectiveIndex => vec![Role::ArgumentIsFiniteSet],
        BuiltinTheoremId::RationalHasUniqueReducedFraction => {
            vec![Role::ArgumentBelongsToRationals]
        }
        BuiltinTheoremId::FunctionSetMember => vec![Role::FunctionSignatureMatchesTarget],
        BuiltinTheoremId::SetBuilderMember => vec![Role::SetBuilderDefiningFacts],
        BuiltinTheoremId::DefinedSetMember => vec![Role::DefinedSetMembership],
        BuiltinTheoremId::StructMember => vec![Role::StructCarrierFacts],
        BuiltinTheoremId::CartesianMemberFromCoordinates => vec![Role::CartesianCoordinates],
        BuiltinTheoremId::GeneralCartesianMember => {
            vec![Role::GeneralCartesianPointwiseMembership]
        }
        BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromFamily => {
            vec![Role::GeneralCartesianFamilyNonempty]
        }
        BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromPointwise => {
            vec![Role::GeneralCartesianPointwiseNonempty]
        }
        BuiltinTheoremId::SumLessEqualFromPointwise => vec![Role::IntegerSumPointwiseOrder],
        BuiltinTheoremId::FiniteSetSumLessEqualFromPointwise => {
            vec![Role::FiniteSetSumPointwiseOrder]
        }
        BuiltinTheoremId::FiniteSetSummandLessEqualSum => {
            vec![Role::FiniteSetSummandNonnegative]
        }
        BuiltinTheoremId::TupleEqualFromCoordinates => vec![Role::TupleCoordinatesEqual],
        BuiltinTheoremId::FiniteSetSumSubstitution => vec![Role::FiniteSetSumSubstitution],
        BuiltinTheoremId::SumOverBijectiveFiniteSetEnumerations => {
            vec![Role::BijectiveFiniteSetEnumerations]
        }
        BuiltinTheoremId::RealLeastUpperBoundExists => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::ArgumentSetIsNonempty,
            Role::SuppliedUpperBoundBelongsToReals,
            Role::SuppliedValueBoundsEverySetMember,
        ],
        BuiltinTheoremId::RealMemberLeLeastUpperBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealLeastUpperBound,
            Role::ArgumentIsMemberOfSet,
        ],
        BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealLeastUpperBound,
            Role::SuppliedUpperBoundBelongsToReals,
            Role::SuppliedValueBoundsEverySetMember,
        ],
        BuiltinTheoremId::RealGreatestLowerBoundExists => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::ArgumentSetIsNonempty,
            Role::SuppliedLowerBoundBelongsToReals,
            Role::SuppliedValueIsLowerBoundForEverySetMember,
        ],
        BuiltinTheoremId::RealGreatestLowerBoundLeMember => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealGreatestLowerBound,
            Role::ArgumentIsMemberOfSet,
        ],
        BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealGreatestLowerBound,
            Role::SuppliedLowerBoundBelongsToReals,
            Role::SuppliedValueIsLowerBoundForEverySetMember,
        ],
        BuiltinTheoremId::RealArchimedeanNaturalUpperBound => {
            vec![Role::ArgumentBelongsToReals]
        }
        BuiltinTheoremId::RationalBetweenReals => vec![
            Role::LeftArgumentBelongsToReals,
            Role::RightArgumentBelongsToReals,
            Role::RealArgumentsStrictlyOrdered,
        ],
    }
}
