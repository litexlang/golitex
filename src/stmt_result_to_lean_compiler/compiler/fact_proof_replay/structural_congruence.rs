//! Structural known-equality and definition congruence.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_structural_known_equality_congruence_from_result(
        &mut self,
        target: &Fact,
        evidence: &StructuralKnownEqualityCongruenceBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("structural-known-equality evidence changed its target".into());
        }
        if subgoals.is_empty() {
            return Err("structural-known-equality evidence retained no child Result".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            return Err("structural-known-equality evidence targets a non-equality fact".into());
        };

        fn replay(
            compiler: &mut StmtResultToLeanCompiler,
            left: &Obj,
            right: &Obj,
            line_file: &LineFile,
            subgoals: &[VerifyFactResult],
            next_subgoal: &mut usize,
            integer_identity_to_complex: bool,
        ) -> Result<String, String> {
            let renders_as_exact_integer = |object: &Obj,
                                            compiler: &StmtResultToLeanCompiler|
             -> bool {
                let Ok(rendered) = render_obj(object, &compiler.environment_stack) else {
                    return false;
                };
                let Ok(integer) = render_integer_obj(object, &compiler.environment_stack) else {
                    return false;
                };
                rendered == integer
            };
            if objs_equal_with_nested_binder_alpha_equivalence(left, right) {
                if integer_identity_to_complex {
                    return Ok(format!(
                        "Litex.Same.intComplex ({})",
                        render_integer_obj(left, &compiler.environment_stack)?
                    ));
                }
                return Ok(format!(
                    "Litex.Same.refl ({})",
                    render_obj(left, &compiler.environment_stack)?
                ));
            }
            if let (Obj::Add(left_add), Obj::Add(right_add)) = (left, right) {
                let source_left_integer =
                    renders_as_exact_integer(left_add.left.as_ref(), compiler);
                let source_right_integer =
                    renders_as_exact_integer(left_add.right.as_ref(), compiler);
                let target_left_integer =
                    renders_as_exact_integer(right_add.left.as_ref(), compiler);
                let target_right_integer =
                    renders_as_exact_integer(right_add.right.as_ref(), compiler);
                let source_is_integer_add = source_left_integer && source_right_integer;
                let target_is_integer_add = target_left_integer && target_right_integer;
                let source_is_complex_plus_integer = !source_left_integer && source_right_integer;
                let child_integer_identity_to_complex =
                    source_is_integer_add && !target_is_integer_add;
                let left_proof = replay(
                    compiler,
                    left_add.left.as_ref(),
                    right_add.left.as_ref(),
                    line_file,
                    subgoals,
                    next_subgoal,
                    child_integer_identity_to_complex && target_left_integer,
                )?;
                let right_proof = replay(
                    compiler,
                    left_add.right.as_ref(),
                    right_add.right.as_ref(),
                    line_file,
                    subgoals,
                    next_subgoal,
                    (child_integer_identity_to_complex && target_right_integer)
                        || (source_is_complex_plus_integer && target_right_integer),
                )?;
                let theorem = if source_is_integer_add && target_is_integer_add {
                    "Litex.Same.intAddCongr"
                } else if source_is_integer_add {
                    "Litex.Same.intCastAddComplex"
                } else if source_is_complex_plus_integer {
                    "Litex.Same.addCongrRightInt"
                } else {
                    "Litex.Same.addCongr"
                };
                return Ok(format!("{theorem} ({left_proof}) ({right_proof})"));
            }

            let expected: Fact = compiler
                .runtime
                .new_equal_fact_from_refs(left, right, line_file.clone())
                .into();
            let child = subgoals.get(*next_subgoal).ok_or_else(|| {
                "structural-known-equality evidence has fewer child Results than leaves".to_string()
            })?;
            *next_subgoal += 1;
            compiler.construct_lean_proof_from_fact_result_without_storing(
                child,
                &expected,
                "structural-known-equality leaf",
            )
        }

        let mut next_subgoal = 0;
        let proof = replay(
            self,
            &equality.left,
            &equality.right,
            &equality.line_file,
            subgoals,
            &mut next_subgoal,
            false,
        )?;
        if next_subgoal != subgoals.len() {
            return Err("structural-known-equality evidence retained unused child Results".into());
        }
        render_fact(target, &self.environment_stack)?;
        Ok(Some(proof))
    }

    pub(in super::super) fn construct_lean_structural_definition_congruence_from_result(
        &self,
        target: &Fact,
        evidence: &StructuralDefinitionCongruenceBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("structural-definition evidence changed its target".into());
        }
        if !subgoals.is_empty() {
            return Err("structural-definition evidence unexpectedly gained child Results".into());
        }
        if evidence.reductions.is_empty() {
            return Err("structural-definition evidence retained no definition reduction".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            return Err("structural-definition evidence targets a non-equality fact".into());
        };

        let mut definition_names = Vec::new();
        for (index, reduction) in evidence.reductions.iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) =
                &reduction.defining_equality
            else {
                return Err(format!(
                    "structural definition reduction {index} retained a non-equality source"
                ));
            };
            if obj_equality_key(&defining_equality.left)
                != obj_equality_key(&reduction.definition_object)
                || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
            {
                return Err(format!(
                    "structural definition reduction {index} changed its defining equality"
                ));
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
                        "structural definition reduction {index} references unavailable defining FactId `{}`",
                        reduction.defining_equality_fact_id
                    )
                })?;
            if !object_is_symbol(&reduction.definition_object, binding.symbol_id) {
                return Err(format!(
                    "structural definition reduction {index} changed its function symbol"
                ));
            }
            let Obj::FnObj(application) = &reduction.application else {
                return Err(format!(
                    "structural definition reduction {index} retained a non-application"
                ));
            };
            let application_head: Obj = application.head.as_ref().clone().into();
            if !object_is_symbol(&application_head, binding.symbol_id)
                || application.body.len() != 1
                || application.body[0].len() != binding.function.parameters.len()
            {
                return Err(format!(
                    "structural definition reduction {index} changed its application telescope"
                ));
            }
            let substitutions = binding
                .function
                .parameters
                .iter()
                .zip(application.body[0].iter())
                .map(|(parameter, argument)| {
                    (
                        parameter.symbol_id.substitution_key(),
                        argument.as_ref().clone(),
                    )
                })
                .collect::<HashMap<_, _>>();
            let reproduced = Runtime::default()
                .inst_obj(
                    &binding.source_body,
                    &substitutions,
                    SubstitutionMode::Named,
                )
                .map_err(|error| {
                    format!(
                        "structural definition reduction {index} could not replay substitution: {}",
                        error.trace_message()
                    )
                })?;
            if !objs_equal_with_nested_binder_alpha_equivalence(&reproduced, &reduction.reduced) {
                return Err(format!(
                    "structural definition reduction {index} changed its substituted body"
                ));
            }
            if !definition_names.contains(&binding.name) {
                definition_names.push(binding.name.clone());
            }
        }

        fn endpoints_align(
            left: &Obj,
            right: &Obj,
            reductions: &[NestedCheckedFunctionDefinitionReductionEvidence],
            uses: &mut [usize],
        ) -> bool {
            if objs_equal_with_nested_binder_alpha_equivalence(left, right) {
                return true;
            }
            for (index, reduction) in reductions.iter().enumerate() {
                if obj_equality_key(left) == obj_equality_key(&reduction.application) {
                    uses[index] += 1;
                    return endpoints_align(&reduction.reduced, right, reductions, uses);
                }
                if obj_equality_key(right) == obj_equality_key(&reduction.application) {
                    uses[index] += 1;
                    return endpoints_align(left, &reduction.reduced, reductions, uses);
                }
            }
            let comparison: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
                left,
                right,
                &mut |left, right| Ok(endpoints_align(left, right, reductions, uses)),
            );
            comparison.unwrap_or(false)
        }

        let mut uses = vec![0usize; evidence.reductions.len()];
        if !endpoints_align(
            &equality.left,
            &equality.right,
            &evidence.reductions,
            &mut uses,
        ) || uses.iter().any(|count| *count != 1)
        {
            return Err(
                "structural-definition evidence does not replay its exact equality once".into(),
            );
        }
        render_fact(target, &self.environment_stack)?;
        Ok(Some(format!(
            "(by\n  unfold Litex.fnApplyOwn {}\n  exact Litex.Same.refl _)",
            definition_names.join(" ")
        )))
    }
}
