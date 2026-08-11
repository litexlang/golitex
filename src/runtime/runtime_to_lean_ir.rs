use crate::prelude::*;
use crate::to_lean_ir::{RegisteredRuleApplicationToLeanIR, TypedBoundObjToLeanIR};
use crate::verify::local_builtin_catalog::registered_local_builtin_rules;
use crate::verify::rule_schema::{
    canonical_atomic_facts_equal, canonical_objs_equal, match_conclusion, MatchLimits,
};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
struct ToLeanIrContext {
    local_fact_ids: HashMap<String, FactId>,
}

impl ToLeanIrContext {
    fn with_infer_result(&self, infer_result: &InferResult) -> Self {
        let mut nested = self.clone();
        for output in infer_result.store_fact_outputs.iter() {
            if let Some(fact_id) = output.fact_id {
                nested.local_fact_ids.insert(
                    output.itself_and_why_itself_is_stored.0.to_string(),
                    fact_id,
                );
            }
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                if let Some(fact_id) = fact_id {
                    nested.local_fact_ids.insert(fact.to_string(), *fact_id);
                }
            }
        }
        nested
    }
}

impl Runtime {
    pub(crate) fn build_stmt_to_lean_ir(
        &self,
        result: &StmtResult,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        if let Some(success) = result.factual_success() {
            ensure_fact_objects_lower_to_lean_ir(&success.stmt)?;
            let fact = self.fact_to_lean_ir_from_success(success)?;
            let excluded = HashSet::from([success.stmt.to_string()]);
            if success.fact_id.is_none() {
                return self.projected_forall_stmt_to_lean_ir(success, fact, excluded);
            }
            return Ok(StmtToLeanIR::Fact(FactStmtToLeanIR {
                fact,
                inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &excluded)?,
            }));
        }

        let Some(success) = result.non_factual_success() else {
            return Err(to_lean_ir_error(
                &result.line_file(),
                "To-Lean IR requires a successful statement result",
            ));
        };
        match &success.stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(stmt)) => {
                Ok(StmtToLeanIR::AbstractProp(AbstractPropToLeanIR {
                    name: stmt.name.clone(),
                    params: stmt.params.clone(),
                }))
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(stmt)) => {
                for fact in stmt.iff_facts.iter() {
                    ensure_fact_objects_lower_to_lean_ir(fact)?;
                }
                Ok(StmtToLeanIR::Prop(PropToLeanIR {
                    name: stmt.name.clone(),
                    params: stmt
                        .params_def_with_type
                        .groups
                        .iter()
                        .map(param_group_to_lean_ir)
                        .collect::<Result<Vec<_>, RuntimeError>>()?,
                    iff_facts: stmt.iff_facts.clone(),
                }))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(stmt)) => {
                self.have_obj_equal_stmt_to_lean_ir(stmt, success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(stmt)) => {
                self.have_obj_choice_stmt_to_lean_ir(stmt, success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(stmt)) => self
                .have_existential_witness_to_lean_ir(
                    &stmt.equal_to_bindings,
                    &stmt.exist_fact_in_have_obj_st,
                    &stmt.line_file,
                    success,
                ),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(stmt)) => {
                let body = ExistFactBody::new(
                    stmt.param_def.clone(),
                    stmt.facts.clone(),
                    stmt.line_file.clone(),
                )?;
                self.have_existential_witness_to_lean_ir(
                    &stmt.param_def.collect_param_bindings(),
                    &ExistFactEnum::ExistFact(body),
                    &stmt.line_file,
                    success,
                )
            }
            Stmt::Witness(WitnessStmt::WitnessExistFact(stmt)) => {
                self.witness_exist_stmt_to_lean_ir(stmt, success)
            }
            Stmt::By(ByStmt::ByCasesStmt(stmt)) => self.by_cases_stmt_to_lean_ir(stmt, success),
            Stmt::By(ByStmt::ByContraStmt(stmt)) => self.by_contra_stmt_to_lean_ir(stmt, success),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(stmt)) => {
                let excluded = stmt
                    .facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<HashSet<_>>();
                let mut facts = Vec::with_capacity(stmt.facts.len());
                for fact in stmt.facts.iter() {
                    ensure_fact_objects_lower_to_lean_ir(fact)?;
                    facts.push(FactToLeanIR {
                        fact_id: self.known_fact_id_for_fact(fact)?,
                        proposition: fact.clone(),
                        proof: FactProofToLeanIR::Trusted,
                    });
                }
                Ok(StmtToLeanIR::Trust(TrustToLeanIR {
                    facts,
                    inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &excluded)?,
                }))
            }
            other => Err(to_lean_ir_error(
                &other.line_file(),
                format!(
                    "To-Lean IR MVP does not support statement kind `{}`",
                    other.stmt_type_name()
                ),
            )),
        }
    }

    fn witness_exist_stmt_to_lean_ir(
        &self,
        stmt: &WitnessExistFact,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Some(verification) = success.witness_exist_verification.as_ref() else {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "existential witness has no structured introduction verification result",
            ));
        };
        if !stmt.exist_fact_in_witness.is_plain_exist() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "the current To-Lean witness tranche supports positive `exist`, not `exist!` or `not exist`",
            ));
        }
        let param_defs = stmt.exist_fact_in_witness.params_def_with_type();
        let parameter_count = param_defs.number_of_params();
        if parameter_count == 0
            || parameter_count != stmt.equal_tos.len()
            || parameter_count != verification.parameter_checks.len()
            || stmt.exist_fact_in_witness.facts().len() != verification.body_check_indices.len()
            || verification.proof_step_count != stmt.proof.len()
            || verification.uniqueness_check_index.is_some()
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "existential witness evidence has inconsistent parameter, proof-step, body, or uniqueness mappings",
            ));
        }
        if success
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "existential witness inferred consequences are not represented by this To-Lean tranche",
            ));
        }

        let existential: Fact = stmt.exist_fact_in_witness.clone().into();
        ensure_fact_objects_lower_to_lean_ir(&existential)?;
        if success.infers.store_fact_outputs.len() != 1
            || success.infers.store_fact_outputs[0]
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != existential.to_string()
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "existential witness stored facts do not match its introduced existential",
            ));
        }

        let proof_steps = success
            .inside_results
            .get(..verification.proof_step_count)
            .ok_or_else(|| {
                to_lean_ir_error(
                    &stmt.line_file,
                    "existential witness proof-step range points outside retained results",
                )
            })?
            .iter()
            .map(|result| self.nested_stmt_to_lean_ir(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;

        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            param_defs,
            &stmt.equal_tos,
            ParamObjType::Exist,
        )?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let mut parameter_requirements = Vec::new();
        let mut used_result_indices = (0..verification.proof_step_count).collect::<HashSet<_>>();
        for (index, ((witness, param_type), check_result)) in stmt
            .equal_tos
            .iter()
            .zip(flat_types.iter())
            .zip(verification.parameter_checks.iter())
            .enumerate()
        {
            ObjToLeanIR::lower(witness)
                .map_err(|message| to_lean_ir_error(&stmt.line_file, message))?;
            if matches!(param_type, ParamType::Set(_)) {
                if check_result.is_some() {
                    return Err(to_lean_ir_error(
                        &stmt.line_file,
                        format!(
                            "existential witness parameter {} retained an unnecessary `set` requirement",
                            index + 1
                        ),
                    ));
                }
                continue;
            }
            let Some(check_result) = check_result else {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "existential witness parameter {} is missing its checked type requirement",
                        index + 1
                    ),
                ));
            };
            let expected =
                object_type_fact_for_to_lean(witness.clone(), param_type, stmt.line_file.clone());
            let mut requirement = self.fact_to_lean_ir_from_result(
                check_result.as_ref(),
                "existential witness parameter requirement",
                &ToLeanIrContext::default(),
            )?;
            if requirement.proposition.to_string() != expected.to_string() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "existential witness type check `{}` does not match expected `{}`",
                        requirement.proposition, expected
                    ),
                ));
            }
            requirement.fact_id = None;
            parameter_requirements.push(requirement);
        }

        let param_to_obj_map =
            param_defs.param_defs_and_args_to_param_to_arg_map(stmt.equal_tos.as_slice());
        let mut body_premises = Vec::with_capacity(stmt.exist_fact_in_witness.facts().len());
        for (body_index, (body, result_index)) in stmt
            .exist_fact_in_witness
            .facts()
            .iter()
            .zip(verification.body_check_indices.iter())
            .enumerate()
        {
            if !used_result_indices.insert(*result_index) {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    "existential witness reuses a retained result for multiple evidence roles",
                ));
            }
            let expected = self
                .inst_exist_body_fact(body, &param_to_obj_map, ParamObjType::Exist, None)?
                .to_fact();
            let mut premise = self.fact_to_lean_ir_from_result(
                success.inside_results.get(*result_index).ok_or_else(|| {
                    to_lean_ir_error(
                        &stmt.line_file,
                        "existential witness body-check index points outside retained results",
                    )
                })?,
                "existential witness body requirement",
                &ToLeanIrContext::default(),
            )?;
            if premise.proposition.to_string() != expected.to_string() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "existential witness body check {} `{}` does not match expected `{}`",
                        body_index + 1,
                        premise.proposition,
                        expected
                    ),
                ));
            }
            premise.fact_id = None;
            body_premises.push(premise);
        }
        if used_result_indices.len() != success.inside_results.len() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "existential witness retained results are not exhausted by its structured evidence mapping",
            ));
        }

        let expected_parameter_requirements = parameter_requirements
            .iter()
            .map(|requirement| requirement.proposition.clone())
            .collect();
        let expected_body_facts = body_premises
            .iter()
            .map(|premise| premise.proposition.clone())
            .collect();

        Ok(StmtToLeanIR::Proof(ProofStmtToLeanIR {
            facts: vec![FactToLeanIR {
                fact_id: Some(stored_fact_id_from_infer_result(
                    &success.infers,
                    &existential,
                    "existential witness fact",
                )?),
                proposition: existential,
                proof: FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::ExistIntroduction {
                        witnesses: stmt.equal_tos.clone(),
                        steps: proof_steps,
                        expected_parameter_requirements,
                        expected_body_facts,
                    },
                    parameter_requirements,
                    premises: body_premises,
                },
            }],
            inferred_facts: Vec::new(),
        }))
    }

    fn have_existential_witness_to_lean_ir(
        &self,
        bindings: &[SymbolBinding],
        exist_fact: &ExistFactEnum,
        line_file: &LineFile,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Some(verification) = success.existential_elimination_verification.as_ref() else {
            return Err(to_lean_ir_error(
                line_file,
                "existential elimination has no structured source-to-projection verification result",
            ));
        };
        if !exist_fact.is_plain_exist() || verification.includes_uniqueness {
            return Err(to_lean_ir_error(
                line_file,
                "the current To-Lean elimination tranche supports positive `exist`, not `exist!` or `not exist`",
            ));
        }
        if bindings.is_empty()
            || bindings.len() != exist_fact.params_def_with_type().number_of_params()
            || bindings.len() != verification.witness_type_facts.len()
            || exist_fact.facts().len() != verification.instantiated_body_facts.len()
        {
            return Err(to_lean_ir_error(
                line_file,
                "existential elimination evidence has inconsistent witness, type-fact, or body-fact mappings",
            ));
        }
        if success.inside_results.len() != 1 || verification.source_result_index != 0 {
            return Err(to_lean_ir_error(
                line_file,
                "existential elimination must retain exactly one source proof at index zero",
            ));
        }
        if success
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(to_lean_ir_error(
                line_file,
                "existential elimination inferred consequences are not represented by this To-Lean tranche",
            ));
        }

        let source_proposition: Fact = exist_fact.clone().into();
        ensure_fact_objects_lower_to_lean_ir(&source_proposition)?;
        let mut source = self.fact_to_lean_ir_from_result(
            &success.inside_results[verification.source_result_index],
            "existential elimination source proof",
            &ToLeanIrContext::default(),
        )?;
        if source.proposition.to_string() != source_proposition.to_string() {
            return Err(to_lean_ir_error(
                line_file,
                format!(
                    "existential elimination source `{}` does not certify `{}`",
                    source.proposition, source_proposition
                ),
            ));
        }
        source.fact_id = None;

        let witness_objs = bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect::<Vec<Obj>>();
        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            exist_fact.params_def_with_type(),
            &witness_objs,
            ParamObjType::Exist,
        )?;
        let flat_types = exist_fact
            .params_def_with_type()
            .flat_instantiated_types_for_args(&instantiated_types);
        let mut witnesses = Vec::with_capacity(bindings.len());
        let mut projections = Vec::with_capacity(
            verification.witness_type_facts.len() + verification.instantiated_body_facts.len(),
        );
        let mut expected_fact_keys = HashSet::new();
        for (witness_index, ((binding, param_type), expected)) in bindings
            .iter()
            .zip(flat_types.iter())
            .zip(verification.witness_type_facts.iter())
            .enumerate()
        {
            let calculated = object_type_fact_for_to_lean(
                witness_objs[witness_index].clone(),
                param_type,
                line_file.clone(),
            );
            if calculated.to_string() != expected.to_string() {
                return Err(to_lean_ir_error(
                    line_file,
                    format!(
                        "existential elimination stored type fact `{}` does not match expected `{}`",
                        expected, calculated
                    ),
                ));
            }
            ensure_fact_objects_lower_to_lean_ir(expected)?;
            let fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                expected,
                "existential elimination witness type fact",
            )?;
            if !expected_fact_keys.insert(expected.to_string()) {
                return Err(to_lean_ir_error(
                    line_file,
                    "existential elimination emitted duplicate projection facts",
                ));
            }
            witnesses.push(ExistentialWitnessToLeanIR {
                symbol_id: binding.id(),
                name: binding.name().to_string(),
                param_type: param_type_to_lean_ir(param_type, binding.id())?,
            });
            projections.push(FactToLeanIR {
                fact_id: Some(fact_id),
                proposition: expected.clone(),
                proof: FactProofToLeanIR::ExistentialElimination {
                    source_proposition: source_proposition.clone(),
                    role: ExistentialProjectionRoleToLeanIR::ParameterType { witness_index },
                    expected_proposition: expected.clone(),
                },
            });
        }

        let param_to_obj_map = exist_fact
            .params_def_with_type()
            .param_defs_and_args_to_param_to_arg_map(&witness_objs);
        for (body_index, (body, expected)) in exist_fact
            .facts()
            .iter()
            .zip(verification.instantiated_body_facts.iter())
            .enumerate()
        {
            let calculated = self
                .inst_exist_body_fact(body, &param_to_obj_map, ParamObjType::Exist, None)?
                .to_fact();
            if calculated.to_string() != expected.to_string() {
                return Err(to_lean_ir_error(
                    line_file,
                    format!(
                        "existential elimination stored body fact `{}` does not match expected `{}`",
                        expected, calculated
                    ),
                ));
            }
            ensure_fact_objects_lower_to_lean_ir(expected)?;
            let fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                expected,
                "existential elimination body fact",
            )?;
            if !expected_fact_keys.insert(expected.to_string()) {
                return Err(to_lean_ir_error(
                    line_file,
                    "existential elimination emitted duplicate projection facts",
                ));
            }
            projections.push(FactToLeanIR {
                fact_id: Some(fact_id),
                proposition: expected.clone(),
                proof: FactProofToLeanIR::ExistentialElimination {
                    source_proposition: source_proposition.clone(),
                    role: ExistentialProjectionRoleToLeanIR::BodyFact { body_index },
                    expected_proposition: expected.clone(),
                },
            });
        }

        if success.infers.store_fact_outputs.len() != expected_fact_keys.len()
            || success.infers.store_fact_outputs.iter().any(|output| {
                !expected_fact_keys.contains(&output.itself_and_why_itself_is_stored.0.to_string())
            })
        {
            return Err(to_lean_ir_error(
                line_file,
                "existential elimination stored facts do not match its type-and-body projection contract",
            ));
        }

        Ok(StmtToLeanIR::HaveExistentialWitness(
            HaveExistentialWitnessToLeanIR {
                source,
                witnesses,
                projections,
            },
        ))
    }

    fn have_obj_choice_stmt_to_lean_ir(
        &self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Some(verification) = success.object_choice_verification.as_ref() else {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "object choice has no structured nonemptiness-to-membership verification result",
            ));
        };
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if bindings_with_types.len() != verification.selected_type_facts.len()
            || bindings_with_types.len() != verification.nonempty_check_indices.len()
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "object choice evidence has inconsistent binding, type-fact, or nonemptiness mappings",
            ));
        }
        if success
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "object choice inferred consequences are not represented by this To-Lean tranche",
            ));
        }

        let mut expected_fact_keys = HashSet::new();
        let mut choices = Vec::with_capacity(bindings_with_types.len());
        for (index, (binding, param_type)) in bindings_with_types.iter().enumerate() {
            let ParamType::Obj(carrier) = param_type else {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "object choice from meta-level parameter type `{}` has no checked inhabited-type backend",
                        param_type
                    ),
                ));
            };
            let Some(check_index) = verification.nonempty_check_indices[index] else {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    "object-carrier choice did not retain a nonemptiness proof index",
                ));
            };
            let Some(check_result) = success.inside_results.get(check_index) else {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    "object-carrier choice points outside its retained nonemptiness proofs",
                ));
            };
            let expected_nonempty: Fact =
                IsNonemptySetFact::new(carrier.clone(), stmt.line_file.clone()).into();
            let mut nonempty_proof = self.fact_to_lean_ir_from_result(
                check_result,
                "object-choice nonemptiness proof",
                &ToLeanIrContext::default(),
            )?;
            if nonempty_proof.proposition.to_string() != expected_nonempty.to_string() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "object-choice proof `{}` does not certify selected carrier `{}`",
                        nonempty_proof.proposition, carrier
                    ),
                ));
            }
            nonempty_proof.fact_id = None;

            let definition_name = binding.name().to_string();
            let defined_obj: Obj =
                Identifier::new_bound(definition_name.clone(), binding.as_ref()).into();
            let expected_membership =
                object_type_fact_for_to_lean(defined_obj, param_type, stmt.line_file.clone());
            let selected_type_fact = &verification.selected_type_facts[index];
            if selected_type_fact.to_string() != expected_membership.to_string() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "object-choice stored type fact `{}` does not match expected membership `{}`",
                        selected_type_fact, expected_membership
                    ),
                ));
            }
            let membership_fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                selected_type_fact,
                "object-choice membership fact",
            )?;
            expected_fact_keys.insert(selected_type_fact.to_string());
            let carrier_ir = ObjToLeanIR::lower(carrier)
                .map_err(|message| to_lean_ir_error(&stmt.line_file, message))?;
            choices.push(ObjectChoiceToLeanIR {
                symbol_id: binding.id(),
                name: definition_name.clone(),
                carrier: carrier_ir.clone(),
                nonempty_proof,
                membership: FactToLeanIR {
                    fact_id: Some(membership_fact_id),
                    proposition: selected_type_fact.clone(),
                    proof: FactProofToLeanIR::ObjectChoice {
                        definition: definition_name,
                        carrier: carrier_ir,
                    },
                },
            });
        }

        if success.infers.store_fact_outputs.len() != expected_fact_keys.len()
            || success.infers.store_fact_outputs.iter().any(|output| {
                !expected_fact_keys.contains(&output.itself_and_why_itself_is_stored.0.to_string())
            })
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "object-choice stored facts do not match its selected membership contract",
            ));
        }

        Ok(StmtToLeanIR::HaveObjChoice(HaveObjChoiceToLeanIR {
            choices,
        }))
    }

    fn have_obj_equal_stmt_to_lean_ir(
        &self,
        stmt: &HaveObjEqualStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if bindings_with_types.len() != stmt.objs_equal_to.len()
            || bindings_with_types.len() != success.inside_results.len()
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "have-object equality evidence has inconsistent binding, value, or type-check counts",
            ));
        }

        if success
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "have-object equality inferred consequences are not represented by this To-Lean tranche",
            ));
        }

        let mut definitions = Vec::with_capacity(bindings_with_types.len());
        let mut facts = Vec::with_capacity(bindings_with_types.len() * 2);
        let mut expected_fact_keys = HashSet::new();

        for (index, ((binding, param_type), value)) in bindings_with_types
            .iter()
            .zip(stmt.objs_equal_to.iter())
            .enumerate()
        {
            let definition_name = binding.name().to_string();
            let defined_obj: Obj =
                Identifier::new_bound(definition_name.clone(), binding.as_ref()).into();
            let value_type_fact =
                object_type_fact_for_to_lean(value.clone(), param_type, stmt.line_file.clone());
            let stored_type_fact = object_type_fact_for_to_lean(
                defined_obj.clone(),
                param_type,
                stmt.line_file.clone(),
            );
            let stored_equality: Fact =
                EqualFact::new(defined_obj, value.clone(), stmt.line_file.clone()).into();

            let mut value_check = self.fact_to_lean_ir_from_result(
                &success.inside_results[index],
                "have-object value type check",
                &ToLeanIrContext::default(),
            )?;
            if value_check.proposition.to_string() != value_type_fact.to_string() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "have-object value check `{}` does not match expected `{}`",
                        value_check.proposition, value_type_fact
                    ),
                ));
            }
            value_check.fact_id = None;

            let stored_type_fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                &stored_type_fact,
                "have-object type fact",
            )?;
            let stored_equality_fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                &stored_equality,
                "have-object defining equality",
            )?;
            expected_fact_keys.insert(stored_type_fact.to_string());
            expected_fact_keys.insert(stored_equality.to_string());

            let value_ir = ObjToLeanIR::lower(value)
                .map_err(|message| to_lean_ir_error(&stmt.line_file, message))?;
            definitions.push(ObjectDefinitionToLeanIR {
                symbol_id: binding.id(),
                name: definition_name.clone(),
                param_type: param_type_to_lean_ir(param_type, binding.id())?,
                value: value_ir.clone(),
            });
            facts.push(FactToLeanIR {
                fact_id: Some(stored_type_fact_id),
                proposition: stored_type_fact,
                proof: FactProofToLeanIR::ObjectDefinition {
                    definition: definition_name.clone(),
                    value: value_ir.clone(),
                    value_check: Some(Box::new(value_check)),
                },
            });
            facts.push(FactToLeanIR {
                fact_id: Some(stored_equality_fact_id),
                proposition: stored_equality,
                proof: FactProofToLeanIR::ObjectDefinition {
                    definition: definition_name,
                    value: value_ir,
                    value_check: None,
                },
            });
        }

        if success.infers.store_fact_outputs.len() != expected_fact_keys.len()
            || success.infers.store_fact_outputs.iter().any(|output| {
                !expected_fact_keys.contains(&output.itself_and_why_itself_is_stored.0.to_string())
            })
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "have-object equality stored facts do not match its type and defining-equality contract",
            ));
        }

        Ok(StmtToLeanIR::HaveObjEqual(HaveObjEqualToLeanIR {
            definitions,
            facts,
        }))
    }

    fn by_cases_stmt_to_lean_ir(
        &self,
        stmt: &ByCasesStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Some(ByVerificationResult::Cases(verification)) = success.by_verification.as_ref()
        else {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-cases statement has no structured verification result",
            ));
        };
        if verification.cases.len() != verification.case_fact_ids.len()
            || verification.cases.len() != verification.case_result_counts.len()
            || verification.cases.len() != verification.proof_step_counts.len()
            || verification.cases.len() != verification.impossible_facts.len()
        {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-cases verification has inconsistent branch metadata",
            ));
        }
        let Some(coverage_result) = success.inside_results.first() else {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-cases verification did not retain its coverage proof",
            ));
        };
        let mut coverage = self.fact_to_lean_ir_from_result(
            coverage_result,
            "by-cases coverage",
            &ToLeanIrContext::default(),
        )?;
        coverage.fact_id = None;
        let expected_coverage: Fact =
            OrFact::new(verification.cases.clone(), stmt.line_file.clone()).into();
        if coverage.proposition.to_string() != expected_coverage.to_string() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                format!(
                    "by-cases coverage `{}` does not match cases `{}`",
                    coverage.proposition, expected_coverage
                ),
            ));
        }

        let mut case_slices = Vec::with_capacity(verification.cases.len());
        let mut cursor: usize = 1;
        for count in verification.case_result_counts.iter().copied() {
            let end = cursor.checked_add(count).ok_or_else(|| {
                to_lean_ir_error(&stmt.line_file, "by-cases result count overflow")
            })?;
            if end > success.inside_results.len() {
                return Err(to_lean_ir_error(
                    &stmt.line_file,
                    "by-cases branch result count exceeds retained results",
                ));
            }
            case_slices.push(&success.inside_results[cursor..end]);
            cursor = end;
        }
        if cursor != success.inside_results.len() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-cases retained results are not fully assigned to branches",
            ));
        }

        let explicit_keys = verification
            .then_facts
            .iter()
            .map(ToString::to_string)
            .collect::<HashSet<_>>();
        let mut facts = Vec::with_capacity(verification.then_facts.len());
        for (goal_index, goal) in verification.then_facts.iter().enumerate() {
            ensure_fact_objects_lower_to_lean_ir(goal)?;
            let mut branches = Vec::with_capacity(verification.cases.len());
            for case_index in 0..verification.cases.len() {
                let case_fact: Fact = verification.cases[case_index].clone().into();
                let case_context = ToLeanIrContext {
                    local_fact_ids: HashMap::from([(
                        case_fact.to_string(),
                        verification.case_fact_ids[case_index],
                    )]),
                };
                let case_results = case_slices[case_index];
                let proof_step_count = verification.proof_step_counts[case_index];
                if proof_step_count > case_results.len() {
                    return Err(to_lean_ir_error(
                        &stmt.line_file,
                        "by-cases proof-step count exceeds retained branch results",
                    ));
                }
                let steps = case_results[..proof_step_count]
                    .iter()
                    .map(|result| self.nested_stmt_to_lean_ir(result))
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let remaining = &case_results[proof_step_count..];
                let exit = if verification.impossible_facts[case_index].is_some() {
                    if remaining.len() != 1 {
                        return Err(to_lean_ir_error(
                            &stmt.line_file,
                            "an impossible by-cases branch must retain one contradiction result",
                        ));
                    }
                    CaseBranchExitToLeanIR::Contradiction(
                        self.wrapped_contradiction_to_lean_ir(
                            &remaining[0],
                            verification.impossible_facts[case_index]
                                .as_ref()
                                .expect("checked above"),
                            &case_context,
                        )?,
                    )
                } else {
                    if remaining.len() != verification.then_facts.len() {
                        return Err(to_lean_ir_error(
                            &stmt.line_file,
                            "a by-cases branch does not retain one result per goal",
                        ));
                    }
                    let mut conclusion = self.fact_to_lean_ir_from_result(
                        &remaining[goal_index],
                        "by-cases branch conclusion",
                        &case_context,
                    )?;
                    if conclusion.proposition.to_string() != goal.to_string() {
                        return Err(to_lean_ir_error(
                            &stmt.line_file,
                            "by-cases branch conclusion does not match its exported goal",
                        ));
                    }
                    conclusion.fact_id = None;
                    CaseBranchExitToLeanIR::Conclusion(conclusion)
                };
                branches.push(CaseBranchToLeanIR {
                    assumption: LocalPremiseToLeanIR::new(
                        verification.case_fact_ids[case_index],
                        case_fact,
                    ),
                    steps,
                    exit,
                });
            }

            facts.push(FactToLeanIR {
                fact_id: Some(stored_fact_id_from_infer_result(
                    &success.infers,
                    goal,
                    "by-cases exported goal",
                )?),
                proposition: goal.clone(),
                proof: FactProofToLeanIR::CaseSplit {
                    coverage: Box::new(coverage.clone()),
                    branches,
                },
            });
        }

        Ok(StmtToLeanIR::Proof(ProofStmtToLeanIR {
            facts,
            inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &explicit_keys)?,
        }))
    }

    fn by_contra_stmt_to_lean_ir(
        &self,
        stmt: &ByContraStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Some(ByVerificationResult::Contra(verification)) = success.by_verification.as_ref()
        else {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-contra statement has no structured verification result",
            ));
        };
        if verification.to_prove.to_string() != stmt.to_prove.to_string() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-contra verification target does not match the statement target",
            ));
        }
        if verification.proof_step_count + 2 != success.inside_results.len() {
            return Err(to_lean_ir_error(
                &stmt.line_file,
                "by-contra must retain its proof steps and two contradiction checks",
            ));
        }
        let reverse_context = ToLeanIrContext {
            local_fact_ids: HashMap::from([(
                verification.reverse_assumption.to_string(),
                verification.reverse_assumption_fact_id,
            )]),
        };
        let steps = success.inside_results[..verification.proof_step_count]
            .iter()
            .map(|result| self.nested_stmt_to_lean_ir(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let contradiction = contradiction_results_to_lean_ir(
            self,
            &success.inside_results[verification.proof_step_count..],
            &verification.impossible_fact,
            &reverse_context,
        )?;
        let explicit_keys = HashSet::from([stmt.to_prove.to_string()]);
        let fact = FactToLeanIR {
            fact_id: Some(stored_fact_id_from_infer_result(
                &success.infers,
                &stmt.to_prove,
                "by-contra exported goal",
            )?),
            proposition: stmt.to_prove.clone(),
            proof: FactProofToLeanIR::ByContradiction {
                reverse_assumption: LocalPremiseToLeanIR::new(
                    verification.reverse_assumption_fact_id,
                    verification.reverse_assumption.clone(),
                ),
                steps,
                contradiction,
            },
        };

        Ok(StmtToLeanIR::Proof(ProofStmtToLeanIR {
            facts: vec![fact],
            inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &explicit_keys)?,
        }))
    }

    fn nested_stmt_to_lean_ir(&self, result: &StmtResult) -> Result<StmtToLeanIR, RuntimeError> {
        match result.to_lean_ir() {
            Some(ir) => Ok(ir.clone()),
            None => self.build_stmt_to_lean_ir(result),
        }
    }

    fn wrapped_contradiction_to_lean_ir(
        &self,
        result: &StmtResult,
        impossible_fact: &AtomicFact,
        context: &ToLeanIrContext,
    ) -> Result<ContradictionToLeanIR, RuntimeError> {
        let Some(success) = result.non_factual_success() else {
            return Err(to_lean_ir_error(
                &result.line_file(),
                "impossible branch did not retain a proof-scope result",
            ));
        };
        contradiction_results_to_lean_ir(self, &success.inside_results, impossible_fact, context)
    }

    fn fact_to_lean_ir_from_success(
        &self,
        success: &FactualStmtSuccess,
    ) -> Result<FactToLeanIR, RuntimeError> {
        self.fact_to_lean_ir_from_success_with_context(success, &ToLeanIrContext::default())
    }

    fn projected_forall_stmt_to_lean_ir(
        &self,
        success: &FactualStmtSuccess,
        source: FactToLeanIR,
        mut excluded: HashSet<String>,
    ) -> Result<StmtToLeanIR, RuntimeError> {
        let Fact::ForallFact(source_forall) = &source.proposition else {
            return Err(to_lean_ir_error(
                &source.proposition.line_file(),
                "a verified non-forall fact was not assigned a stored FactId",
            ));
        };
        let FactProofToLeanIR::ForallIntroduction {
            parameter_premises,
            premises,
            inferred_premises,
            conclusions,
        } = &source.proof
        else {
            return Err(to_lean_ir_error(
                &source.proposition.line_file(),
                "an unstored forall did not retain forall-introduction evidence",
            ));
        };

        let source_bindings = source_forall
            .params_def_with_type
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(move |binding| (binding, &group.param_type))
            })
            .collect::<Vec<_>>();
        if source_bindings.len() != parameter_premises.len()
            || source_forall.then_facts.len() != conclusions.len()
        {
            return Err(to_lean_ir_error(
                &source_forall.line_file,
                "projected forall evidence does not match its source binder or conclusion arity",
            ));
        }

        let source_conclusion_keys = source_forall
            .then_facts
            .iter()
            .map(|fact| fact.clone().to_fact().to_string())
            .collect::<HashSet<_>>();
        let mut facts = Vec::new();
        for output in success.infers.store_fact_outputs.iter() {
            let candidates =
                std::iter::once((&output.itself_and_why_itself_is_stored.0, output.fact_id)).chain(
                    output
                        .inferred_facts
                        .iter()
                        .zip(output.inferred_fact_ids.iter())
                        .map(|(fact, fact_id)| (fact, *fact_id)),
                );
            for (proposition, recorded_fact_id) in candidates {
                if proposition.to_string() == source.proposition.to_string() {
                    continue;
                }
                let Fact::ForallFact(projected) = proposition else {
                    continue;
                };
                if projected.then_facts.is_empty()
                    || projected.then_facts.iter().any(|fact| {
                        !source_conclusion_keys.contains(&fact.clone().to_fact().to_string())
                    })
                    || projected
                        .dom_facts
                        .iter()
                        .map(ToString::to_string)
                        .ne(source_forall.dom_facts.iter().map(ToString::to_string))
                {
                    continue;
                }
                let fact_id = recorded_fact_id.ok_or_else(|| {
                    to_lean_ir_error(
                        &proposition.line_file(),
                        "a stored forall projection reached To-Lean without a FactId",
                    )
                })?;

                let projected_bindings = projected
                    .params_def_with_type
                    .groups
                    .iter()
                    .flat_map(|group| {
                        group
                            .params
                            .iter()
                            .map(move |binding| (binding, &group.param_type))
                    })
                    .collect::<Vec<_>>();
                let mut retained_ids = HashSet::new();
                let mut retained_names = HashSet::new();
                let mut last_source_index = None;
                for (binding, projected_type) in projected_bindings {
                    let Some((source_index, (_, source_type))) = source_bindings
                        .iter()
                        .enumerate()
                        .find(|(_, (source_binding, _))| source_binding.id() == binding.id())
                    else {
                        return Err(to_lean_ir_error(
                            &projected.line_file,
                            "a stored forall projection introduced a new binder",
                        ));
                    };
                    if last_source_index.is_some_and(|last| source_index <= last)
                        || !param_types_match_for_projection(source_type, projected_type)
                    {
                        return Err(to_lean_ir_error(
                            &projected.line_file,
                            "a stored forall projection changed binder order or type",
                        ));
                    }
                    last_source_index = Some(source_index);
                    retained_ids.insert(binding.id());
                    retained_names.insert(binding.name().to_string());
                }

                let projected_parameter_premises = source_bindings
                    .iter()
                    .zip(parameter_premises.iter())
                    .filter(|((binding, _), _)| retained_ids.contains(&binding.id()))
                    .map(|(_, premise)| premise.clone())
                    .collect::<Vec<_>>();
                let mut projected_conclusions = Vec::with_capacity(projected.then_facts.len());
                let mut used_source_conclusions = HashSet::new();
                for projected_conclusion in projected.then_facts.iter() {
                    let projected_key = projected_conclusion.clone().to_fact().to_string();
                    let Some(source_index) = source_forall
                        .then_facts
                        .iter()
                        .enumerate()
                        .find(|(index, source_conclusion)| {
                            !used_source_conclusions.contains(index)
                                && (*source_conclusion).clone().to_fact().to_string()
                                    == projected_key
                        })
                        .map(|(index, _)| index)
                    else {
                        return Err(to_lean_ir_error(
                            &projected.line_file,
                            "a stored forall projection introduced a new conclusion",
                        ));
                    };
                    used_source_conclusions.insert(source_index);
                    projected_conclusions.push(conclusions[source_index].clone());
                }
                if projected_conclusions.is_empty() {
                    return Err(to_lean_ir_error(
                        &projected.line_file,
                        "a stored forall projection has no conclusion",
                    ));
                }

                let projected_inferred_premises = inferred_premises
                    .iter()
                    .filter(|fact| fact_uses_only_forall_params(fact, &retained_names))
                    .cloned()
                    .collect();
                excluded.insert(proposition.to_string());
                facts.push(FactToLeanIR {
                    fact_id: Some(fact_id),
                    proposition: proposition.clone(),
                    proof: FactProofToLeanIR::ForallIntroduction {
                        parameter_premises: projected_parameter_premises,
                        premises: premises.clone(),
                        inferred_premises: projected_inferred_premises,
                        conclusions: projected_conclusions,
                    },
                });
            }
        }
        if facts.is_empty() {
            return Err(to_lean_ir_error(
                &source_forall.line_file,
                "a verified forall had neither a FactId nor stored projections",
            ));
        }

        Ok(StmtToLeanIR::ProjectedForall(ProjectedForallToLeanIR {
            source: source.proposition,
            facts,
            inferred_facts: self.inferred_facts_to_lean_ir(&success.infers, &excluded)?,
        }))
    }

    fn fact_to_lean_ir_from_success_with_context(
        &self,
        success: &FactualStmtSuccess,
        context: &ToLeanIrContext,
    ) -> Result<FactToLeanIR, RuntimeError> {
        Ok(FactToLeanIR {
            fact_id: success.fact_id,
            proposition: success.stmt.clone(),
            proof: self.verified_by_to_lean_ir(
                &success.stmt,
                success.fact_id,
                &success.verified_by,
                context,
            )?,
        })
    }

    fn fact_to_lean_ir_from_result(
        &self,
        result: &StmtResult,
        result_context: &str,
        context: &ToLeanIrContext,
    ) -> Result<FactToLeanIR, RuntimeError> {
        let Some(success) = result.factual_success() else {
            return Ok(FactToLeanIR {
                fact_id: None,
                proposition: result
                    .as_fact_unknown()
                    .map(|unknown| unknown.goal().clone())
                    .unwrap_or_else(|| {
                        NormalAtomicFact::new(
                            AtomicName::WithoutMod("to_lean_unknown_subgoal".to_string()),
                            vec![],
                            result.line_file(),
                        )
                        .into()
                    }),
                proof: FactProofToLeanIR::Unsupported {
                    reason: format!("{} did not return a factual success", result_context),
                },
            });
        };
        self.fact_to_lean_ir_from_success_with_context(success, context)
    }

    fn verified_by_to_lean_ir(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        verified_by: &VerifiedByResult,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => self.builtin_rule_application_to_lean_ir(
                goal,
                &result.msg,
                result.evidence.as_ref(),
                &result.subgoals,
                context,
            ),
            VerifiedByResult::BuiltinStrategy(result) => self.builtin_rule_application_to_lean_ir(
                goal,
                &result.msg,
                result.evidence.as_ref(),
                &result.subgoals,
                context,
            ),
            VerifiedByResult::Fact(result) => match result.cite_what.as_ref() {
                Stmt::Fact(source_fact) => self.fact_citation_to_lean_ir(
                    goal,
                    goal_fact_id,
                    source_fact,
                    result.source_fact_id,
                    result.equality_transport.as_ref(),
                    result.fact_transformation.as_ref(),
                    context,
                ),
                Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                    Ok(FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::DefinitionReduction {
                            definition: definition.name.clone(),
                        },
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
                    })
                }
                Stmt::DefStrategyStmt(strategy) => Ok(FactProofToLeanIR::UserStrategy {
                    name: strategy.name.clone(),
                }),
                cited => Ok(FactProofToLeanIR::Unsupported {
                    reason: format!(
                        "citation kind `{}` is not represented by the To-Lean MVP",
                        cited.stmt_type_name()
                    ),
                }),
            },
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.known_forall_to_lean_ir(goal, result, context)
            }
            VerifiedByResult::VerifiedBys(result) => {
                let mut steps = Vec::with_capacity(result.cite_what.len());
                for step in result.cite_what.iter() {
                    steps.push(self.verified_bys_step_to_lean_ir(
                        step,
                        goal,
                        goal_fact_id,
                        context,
                    )?);
                }
                Ok(FactProofToLeanIR::Composite { steps })
            }
            VerifiedByResult::ForallProof(result) => {
                let parameter_reason = InferReason::ParameterDefinition.store_reason();
                let parameter_premises = result
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| output.itself_and_why_itself_is_stored.1 == parameter_reason)
                    .map(|output| {
                        let fact = output.itself_and_why_itself_is_stored.0.clone();
                        let fact_id = output.fact_id.ok_or_else(|| {
                            to_lean_ir_error(
                                &fact.line_file(),
                                "a forall parameter premise reached To-Lean without a FactId",
                            )
                        })?;
                        Ok(LocalPremiseToLeanIR::new(fact_id, fact))
                    })
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let mut premises = Vec::with_capacity(result.forall_fact.dom_facts.len());
                for dom_fact in result.forall_fact.dom_facts.iter() {
                    let fact = dom_fact.clone();
                    let fact_id = result
                        .assumption_infers
                        .store_fact_outputs
                        .iter()
                        .find(|output| {
                            output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string()
                        })
                        .and_then(|output| output.fact_id)
                        .ok_or_else(|| {
                            to_lean_ir_error(
                                &fact.line_file(),
                                "a forall domain premise reached To-Lean without a FactId",
                            )
                        })?;
                    premises.push(LocalPremiseToLeanIR::new(fact_id, fact));
                }
                let inferred_premises =
                    self.supported_inferred_premises_to_lean_ir(&result.assumption_infers)?;
                let conclusion_context = context.with_infer_result(&result.assumption_infers);
                let mut conclusions = Vec::with_capacity(result.proves.len());
                for proved in result.proves.iter() {
                    conclusions.push(self.fact_to_lean_ir_from_result(
                        proved.result.as_ref(),
                        "forall conclusion",
                        &conclusion_context,
                    )?);
                }
                Ok(FactProofToLeanIR::ForallIntroduction {
                    parameter_premises,
                    premises,
                    inferred_premises,
                    conclusions,
                })
            }
            VerifiedByResult::StatementMemo(source) => Ok(FactProofToLeanIR::Memo {
                proof: Box::new(self.verified_by_to_lean_ir(
                    goal,
                    source.fact_id.or(goal_fact_id),
                    &source.verified_by,
                    context,
                )?),
            }),
        }
    }

    fn fact_citation_to_lean_ir(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        source_fact: &Fact,
        recorded_source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
        fact_transformation: Option<&FactTransformationEvidence>,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let source_fact_id = match recorded_source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, goal, goal_fact_id, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("verified citation `{}` has no stored FactId", source_fact),
            });
        };

        // Preserve the existing closed-membership certificate even when the
        // verifier also records how a differently spelled citation resolved
        // to this closed goal. The checked target rule is dependency-free and
        // more precise than replaying an incidental citation route.
        if source_fact.to_string() != goal.to_string()
            && (crate::to_lean_ir::is_closed_real_membership(goal)
                || crate::to_lean_ir::closed_compact_numeric_set_fact_carrier(goal).is_some())
        {
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: if crate::to_lean_ir::is_closed_real_membership(goal) {
                    ProofRuleToLeanIR::ClosedRealMembership
                } else {
                    ProofRuleToLeanIR::ClosedNumericReflection {
                        carrier: crate::to_lean_ir::closed_compact_numeric_set_fact_carrier(goal)
                            .unwrap(),
                    }
                },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }

        if equality_transport.is_none() && fact_transformation.is_none() {
            if source_fact.to_string() == goal.to_string() {
                return Ok(FactProofToLeanIR::KnownFactCitation { source_fact_id });
            }
            if let (Fact::ExistFact(source_exist), Fact::ExistFact(goal_exist)) =
                (source_fact, goal)
            {
                if source_exist.is_plain_exist()
                    && goal_exist.is_plain_exist()
                    && source_exist.can_be_used_to_verify_goal(goal_exist)
                    && Runtime::exist_fact_normalized_body_string(self, source_exist)?
                        == Runtime::exist_fact_normalized_body_string(self, goal_exist)?
                {
                    return Ok(FactProofToLeanIR::ExistentialAlphaRenameCitation {
                        source_fact_id,
                        source_proposition: source_fact.clone(),
                    });
                }
            }
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::OtherUnsupported {
                    name: format!(
                        "citation `{}` changed goal `{}` without structured rewrite evidence",
                        source_fact, goal
                    ),
                },
                parameter_requirements: Vec::new(),
                premises: vec![FactToLeanIR {
                    fact_id: Some(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: FactProofToLeanIR::KnownFactCitation { source_fact_id },
                }],
            });
        }

        let mut current = FactToLeanIR {
            fact_id: Some(source_fact_id),
            proposition: source_fact.clone(),
            proof: FactProofToLeanIR::KnownFactCitation { source_fact_id },
        };
        let citation_target = fact_transformation
            .map(|transformation| &transformation.source)
            .unwrap_or(goal);
        if let Some(equality_transport) = equality_transport {
            current =
                self.equality_rewrite_fact_to_lean_ir(citation_target, current, equality_transport);
        } else if current.proposition.to_string() != citation_target.to_string() {
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::OtherUnsupported {
                    name: format!(
                        "citation `{}` does not prove transformation source `{}`",
                        source_fact, citation_target
                    ),
                },
                parameter_requirements: Vec::new(),
                premises: vec![current],
            });
        }

        if let Some(transformation) = fact_transformation {
            for step in transformation.steps.iter() {
                current = match &step.rule {
                    FactTransformationRule::RationalNormalization => {
                        if !facts_align_by_rational_normalization(
                            &current.proposition,
                            &step.result,
                        ) {
                            return Ok(FactProofToLeanIR::RuleApplication {
                                rule: ProofRuleToLeanIR::OtherUnsupported {
                                    name: format!(
                                        "normalization source `{}` does not align with result `{}`",
                                        current.proposition, step.result
                                    ),
                                },
                                parameter_requirements: Vec::new(),
                                premises: vec![current],
                            });
                        }
                        FactToLeanIR {
                            fact_id: None,
                            proposition: step.result.clone(),
                            proof: FactProofToLeanIR::RuleApplication {
                                rule: ProofRuleToLeanIR::Normalization {
                                    kind:
                                        NormalizationKindToLeanIR::RationalExpressionSimplification,
                                },
                                parameter_requirements: Vec::new(),
                                premises: vec![current],
                            },
                        }
                    }
                    FactTransformationRule::EqualityRewrite(evidence) => {
                        self.equality_rewrite_fact_to_lean_ir(&step.result, current, evidence)
                    }
                };
            }
        }

        if current.proposition.to_string() != goal.to_string() {
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::OtherUnsupported {
                    name: format!(
                        "fact transformations ended at `{}` instead of goal `{}`",
                        current.proposition, goal
                    ),
                },
                parameter_requirements: Vec::new(),
                premises: vec![current],
            });
        }
        Ok(current.proof)
    }

    fn equality_rewrite_fact_to_lean_ir(
        &self,
        result: &Fact,
        source: FactToLeanIR,
        equality_transport: &EqualityTransportEvidence,
    ) -> FactToLeanIR {
        if equality_transport.steps.is_empty() {
            if source.proposition.to_string() == result.to_string() {
                return source;
            }
            return FactToLeanIR {
                fact_id: None,
                proposition: result.clone(),
                proof: FactProofToLeanIR::Unsupported {
                    reason: format!(
                        "empty equality transport changed `{}` to `{}`",
                        source.proposition, result
                    ),
                },
            };
        }

        let mut premises = Vec::with_capacity(equality_transport.steps.len() + 1);
        premises.push(source);
        let mut steps = Vec::with_capacity(equality_transport.steps.len());
        for rewrite in equality_transport.steps.iter() {
            let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
            let Some(equality_fact_id) = rewrite.equality_fact_id else {
                return FactToLeanIR {
                    fact_id: None,
                    proposition: result.clone(),
                    proof: FactProofToLeanIR::Unsupported {
                        reason: format!(
                            "equality transport `{}` -> `{}` through `{}` has no compiler proof provenance",
                            rewrite.from, rewrite.to, equality_fact
                        ),
                    },
                };
            };
            let left_key = obj_equality_key(&rewrite.equality.left);
            let right_key = obj_equality_key(&rewrite.equality.right);
            let from_key = obj_equality_key(&rewrite.from);
            let to_key = obj_equality_key(&rewrite.to);
            let direction = if from_key == left_key && to_key == right_key {
                EqualityRewriteDirectionToLeanIR::Forward
            } else if from_key == right_key && to_key == left_key {
                EqualityRewriteDirectionToLeanIR::Backward
            } else {
                return FactToLeanIR {
                    fact_id: None,
                    proposition: result.clone(),
                    proof: FactProofToLeanIR::Unsupported {
                        reason: format!(
                            "equality rewrite edge `{}` -> `{}` is not oriented by `{}`",
                            rewrite.from, rewrite.to, equality_fact
                        ),
                    },
                };
            };
            premises.push(FactToLeanIR {
                fact_id: Some(equality_fact_id),
                proposition: equality_fact,
                proof: FactProofToLeanIR::KnownFactCitation {
                    source_fact_id: equality_fact_id,
                },
            });
            steps.push(EqualityRewriteStepToLeanIR {
                from: rewrite.from.clone(),
                to: rewrite.to.clone(),
                direction,
            });
        }

        FactToLeanIR {
            fact_id: None,
            proposition: result.clone(),
            proof: FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::EqualityRewrite(EqualityRewriteToLeanIR { steps }),
                parameter_requirements: Vec::new(),
                premises,
            },
        }
    }

    fn citation_fact_id(
        &self,
        cited_fact: &Fact,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        context: &ToLeanIrContext,
    ) -> Result<Option<FactId>, RuntimeError> {
        if let Some(fact_id) = context.local_fact_ids.get(&cited_fact.to_string()) {
            return Ok(Some(*fact_id));
        }
        if let Some(fact_id) = self.known_fact_id_for_fact(cited_fact)? {
            return Ok(Some(fact_id));
        }
        // A forall conclusion can cite one of its temporary premises. The
        // local environment has already been popped when statement IR is
        // assembled, but verification stored the identical conclusion under
        // the premise's ID and retained that ID on the result.
        if cited_fact.to_string() == goal.to_string() {
            return Ok(goal_fact_id);
        }
        Ok(None)
    }

    fn known_forall_to_lean_ir(
        &self,
        goal: &Fact,
        result: &KnownForallInstantiationResult,
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let Stmt::Fact(source_fact) = result.cite_what.as_ref() else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: "known-forall verification did not cite a fact".to_string(),
            });
        };
        let Fact::ForallFact(source_forall) = source_fact else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: "known-forall verification cited a non-forall fact".to_string(),
            });
        };
        let source_fact_id = match result.source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, source_fact, None, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("known forall `{}` has no stored FactId", source_fact),
            });
        };

        let mut param_types = Vec::new();
        for group in source_forall.params_def_with_type.groups.iter() {
            let Some(anchor) = group.params.first().map(|binding| binding.id()) else {
                return Ok(FactProofToLeanIR::Unsupported {
                    reason: "known forall contains an empty parameter group".to_string(),
                });
            };
            let param_type = param_type_to_lean_ir(&group.param_type, anchor)?;
            for _ in group.params.iter() {
                param_types.push(param_type.clone());
            }
        }
        if result.instantiation.len() != param_types.len() {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` recorded {} arguments for {} parameter types",
                    source_fact,
                    result.instantiation.len(),
                    param_types.len()
                ),
            });
        }
        let arguments = result
            .instantiation
            .iter()
            .zip(param_types)
            .map(|(item, param_type)| KnownForallArgumentToLeanIR {
                param: item.param.clone(),
                argument: item.arg_obj.clone(),
                param_type,
            })
            .collect::<Vec<_>>();
        let mut parameter_requirements = Vec::new();
        let mut requirements = Vec::new();
        for requirement in result.requirements.iter() {
            let requirement_ir = self.fact_to_lean_ir_from_result(
                requirement.result.as_ref(),
                "known-forall requirement",
                context,
            )?;
            match requirement.kind {
                KnownForallRequirementKind::ParameterType => {
                    parameter_requirements.push(requirement_ir)
                }
                KnownForallRequirementKind::Domain => requirements.push(requirement_ir),
            }
        }
        if parameter_requirements.len() != arguments.len() {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` recorded {} arguments but {} parameter requirements",
                    source_fact,
                    arguments.len(),
                    parameter_requirements.len()
                ),
            });
        }

        let Some(source_conclusion) = source_forall.then_facts.first() else {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!("known forall `{}` has no conclusion", source_fact),
            });
        };
        if source_forall.then_facts.len() != 1 {
            return Ok(FactProofToLeanIR::Unsupported {
                reason: format!(
                    "known forall `{}` has {} conclusions instead of one matched conclusion",
                    source_fact,
                    source_forall.then_facts.len()
                ),
            });
        }
        let argument_objects = arguments
            .iter()
            .map(|argument| argument.argument.clone())
            .collect::<Vec<_>>();
        let param_to_arg_map = source_forall
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&argument_objects);
        let instantiated_conclusion = self.inst_fact(
            &source_conclusion.clone().to_fact(),
            &param_to_arg_map,
            ParamObjType::Forall,
            None,
        )?;
        let application = FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::KnownForallInstantiation {
                source_fact_id,
                arguments,
            },
            parameter_requirements,
            premises: requirements,
        };
        if instantiated_conclusion.to_string() == goal.to_string() {
            return Ok(application);
        }

        let instantiated_fact = FactToLeanIR {
            fact_id: None,
            proposition: instantiated_conclusion.clone(),
            proof: application,
        };
        if facts_align_by_rational_normalization(&instantiated_conclusion, goal) {
            return Ok(FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::Normalization {
                    kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                },
                parameter_requirements: Vec::new(),
                premises: vec![instantiated_fact],
            });
        }

        Ok(FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::OtherUnsupported {
                name: format!(
                    "known-forall instance `{}` does not structurally match goal `{}`",
                    instantiated_conclusion, goal
                ),
            },
            parameter_requirements: Vec::new(),
            premises: vec![instantiated_fact],
        })
    }

    fn builtin_rule_application_to_lean_ir(
        &self,
        goal: &Fact,
        label: &str,
        evidence: Option<&BuiltinRuleEvidence>,
        subgoals: &[StmtResult],
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        if let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) = evidence {
            return self.registered_local_builtin_application_to_lean_ir(
                goal, evidence, subgoals, context,
            );
        }
        let rule = match evidence {
            Some(evidence) => ProofRuleToLeanIR::Builtin(
                BuiltinRuleToLeanIR::from_legacy_evidence(evidence).ok_or_else(|| {
                    to_lean_ir_error(
                        &goal.line_file(),
                        "registered local builtin reached legacy evidence lowering",
                    )
                })?,
            ),
            None => ProofRuleToLeanIR::from_verified_builtin_label(label, goal),
        };
        Ok(FactProofToLeanIR::RuleApplication {
            rule,
            parameter_requirements: Vec::new(),
            premises: self.subgoals_to_lean_ir(subgoals, context)?,
        })
    }

    fn registered_local_builtin_application_to_lean_ir(
        &self,
        goal: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
        context: &ToLeanIrContext,
    ) -> Result<FactProofToLeanIR, RuntimeError> {
        let rules = registered_local_builtin_rules()?;
        let rule = rules
            .iter()
            .find(|rule| rule.id() == &evidence.rule_id)
            .ok_or_else(|| {
                to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "unknown local builtin RuleId `{}`",
                        evidence.rule_id.as_str()
                    ),
                )
            })?;
        if rule.semantic_fingerprint() != &evidence.semantic_fingerprint {
            return Err(to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "stale local builtin fingerprint for `{}`",
                    evidence.rule_id.as_str()
                ),
            ));
        }
        if evidence.bindings.len() != rule.schema().variables.len()
            || evidence.parameter_requirement_count != rule.schema().parameter_requirements.len()
        {
            return Err(to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate has the wrong binding or requirement arity",
            ));
        }
        let Fact::AtomicFact(goal_atomic) = goal else {
            return Err(to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate target must be atomic",
            ));
        };
        let matched = match_conclusion(rule.schema(), goal_atomic, MatchLimits::default())
            .map_err(|error| to_lean_ir_error(&goal.line_file(), error.message))?
            .ok_or_else(|| {
                to_lean_ir_error(
                    &goal.line_file(),
                    "local builtin certificate target does not match its registered schema",
                )
            })?;
        for (expected, actual) in matched.bindings().iter().zip(&evidence.bindings) {
            if !canonical_objs_equal(expected, actual, MatchLimits::default())
                .map_err(|error| to_lean_ir_error(&goal.line_file(), error.message))?
            {
                return Err(to_lean_ir_error(
                    &goal.line_file(),
                    "local builtin certificate binding does not match its target",
                ));
            }
        }

        let mut param_to_arg_map = HashMap::new();
        for (variable, binding) in rule.schema().variables.iter().zip(&evidence.bindings) {
            insert_symbol_substitution(&mut param_to_arg_map, &variable.binding, binding.clone());
        }
        let expected_templates = rule
            .schema()
            .parameter_requirements
            .iter()
            .chain(rule.schema().premises.iter())
            .collect::<Vec<_>>();
        if subgoals.len() != expected_templates.len() {
            return Err(to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate has the wrong child-proof arity",
            ));
        }
        let children = self.subgoals_to_lean_ir(subgoals, context)?;
        for (template, child) in expected_templates.iter().zip(&children) {
            let expected = self.inst_atomic_fact(
                template,
                &param_to_arg_map,
                ParamObjType::Forall,
                Some(&goal.line_file()),
            )?;
            let Fact::AtomicFact(actual) = &child.proposition else {
                return Err(to_lean_ir_error(
                    &child.proposition.line_file(),
                    "local builtin child proof is not atomic",
                ));
            };
            if !canonical_atomic_facts_equal(&expected, actual, MatchLimits::default())
                .map_err(|error| to_lean_ir_error(&child.proposition.line_file(), error.message))?
            {
                return Err(to_lean_ir_error(
                    &child.proposition.line_file(),
                    "local builtin child proof does not match its instantiated schema fact",
                ));
            }
        }

        let mut bindings = Vec::with_capacity(evidence.bindings.len());
        for (variable, object) in rule.schema().variables.iter().zip(&evidence.bindings) {
            let object = ObjToLeanIR::lower(object)
                .map_err(|message| to_lean_ir_error(&goal.line_file(), message))?;
            let instantiated_param_type = self.inst_param_type(
                &variable.param_type,
                &param_to_arg_map,
                ParamObjType::Forall,
            )?;
            // This is an occurrence-local carrier view, not a typed Fact IR.
            // A generic set parameter must use the target binding's SymbolId,
            // while a dependent parameter such as `x A` must mention the
            // instantiated target `A`, never the catalog template's symbol.
            let generic_anchor = match &object {
                ObjToLeanIR::Symbol { symbol_id, .. } => *symbol_id,
                _ => variable.binding.id(),
            };
            bindings.push(TypedBoundObjToLeanIR {
                object,
                param_type: param_type_to_lean_ir(&instantiated_param_type, generic_anchor)?,
            });
        }
        let premises = children.split_at(evidence.parameter_requirement_count);
        Ok(FactProofToLeanIR::RuleApplication {
            rule: ProofRuleToLeanIR::RegisteredRule(RegisteredRuleApplicationToLeanIR {
                rule_id: evidence.rule_id.clone(),
                semantic_fingerprint: evidence.semantic_fingerprint.clone(),
                bindings,
                parameter_requirement_count: rule.schema().parameter_requirements.len(),
                premise_count: rule.schema().premises.len(),
            }),
            parameter_requirements: premises.0.to_vec(),
            premises: premises.1.to_vec(),
        })
    }

    fn subgoals_to_lean_ir(
        &self,
        subgoals: &[StmtResult],
        context: &ToLeanIrContext,
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        subgoals
            .iter()
            .map(|result| self.fact_to_lean_ir_from_result(result, "builtin subgoal", context))
            .collect()
    }

    fn verified_bys_step_to_lean_ir(
        &self,
        step: &VerifiedBysEnum,
        enclosing_goal: &Fact,
        enclosing_goal_fact_id: Option<FactId>,
        context: &ToLeanIrContext,
    ) -> Result<FactToLeanIR, RuntimeError> {
        let step_fact_id = |fact: &Fact| -> Result<Option<FactId>, RuntimeError> {
            let known =
                self.citation_fact_id(fact, enclosing_goal, enclosing_goal_fact_id, context)?;
            if known.is_some() || fact.to_string() != enclosing_goal.to_string() {
                Ok(known)
            } else {
                Ok(enclosing_goal_fact_id)
            }
        };
        match step {
            VerifiedBysEnum::ByBuiltinRule(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.builtin_rule_application_to_lean_ir(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByBuiltinStrategy(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.builtin_rule_application_to_lean_ir(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByFact(result) => {
                let proof = match result.cite_what.as_ref() {
                    Stmt::Fact(source) => self.fact_citation_to_lean_ir(
                        &result.verify_what,
                        step_fact_id(&result.verify_what)?,
                        source,
                        result.source_fact_id,
                        result.equality_transport.as_ref(),
                        result.fact_transformation.as_ref(),
                        context,
                    )?,
                    Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) => {
                        FactProofToLeanIR::RuleApplication {
                            rule: ProofRuleToLeanIR::DefinitionReduction {
                                definition: definition.name.clone(),
                            },
                            parameter_requirements: Vec::new(),
                            premises: Vec::new(),
                        }
                    }
                    cited => FactProofToLeanIR::Unsupported {
                        reason: format!("unsupported composite citation `{}`", cited),
                    },
                };
                Ok(FactToLeanIR {
                    fact_id: step_fact_id(&result.verify_what)?,
                    proposition: result.verify_what.clone(),
                    proof,
                })
            }
            VerifiedBysEnum::ByKnownForall(result) => Ok(FactToLeanIR {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.known_forall_to_lean_ir(
                    &result.verify_what,
                    &result.result,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByStatementMemo(goal, source) => Ok(FactToLeanIR {
                fact_id: step_fact_id(goal)?,
                proposition: goal.clone(),
                proof: FactProofToLeanIR::Memo {
                    proof: Box::new(self.verified_by_to_lean_ir(
                        goal,
                        source.fact_id.or(step_fact_id(goal)?),
                        &source.verified_by,
                        context,
                    )?),
                },
            }),
        }
    }

    fn inferred_facts_to_lean_ir(
        &self,
        infer_result: &InferResult,
        excluded: &HashSet<String>,
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        let mut seen = excluded.clone();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            let source_fact = &output.itself_and_why_itself_is_stored.0;
            let source_id = output.fact_id.or(self.known_fact_id_for_fact(source_fact)?);
            let source_key = source_fact.to_string();
            if seen.insert(source_key) {
                let proof = if let Some(carrier) =
                    crate::to_lean_ir::closed_compact_numeric_set_fact_carrier(source_fact)
                {
                    FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::ClosedNumericReflection { carrier },
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
                    }
                } else {
                    FactProofToLeanIR::Inference {
                        source_fact_id: None,
                        reason: output.itself_and_why_itself_is_stored.1.clone(),
                    }
                };
                // Internal inferences are emitted only when this backend has a
                // checked proof adapter. A later citation still fails closed
                // because no Lean declaration is registered for an omitted fact.
                if !matches!(proof, FactProofToLeanIR::Inference { .. }) {
                    inferred.push(FactToLeanIR {
                        fact_id: source_id,
                        proposition: source_fact.clone(),
                        proof,
                    });
                }
            }
            if output.inferred_fact_ids.len() != output.inferred_facts.len() {
                return Err(to_lean_ir_error(
                    &source_fact.line_file(),
                    "inferred fact identity list does not match inferred facts",
                ));
            }
            for (fact, recorded_fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                if !seen.insert(fact.to_string()) {
                    continue;
                }
                let proof = inferred_fact_proof_to_lean_ir(
                    source_fact,
                    source_id,
                    fact,
                    &output.itself_and_why_itself_is_stored.1,
                );
                if matches!(proof, FactProofToLeanIR::Inference { .. }) {
                    continue;
                }
                inferred.push(FactToLeanIR {
                    fact_id: (*recorded_fact_id).or(self.known_fact_id_for_fact(fact)?),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }

    fn supported_inferred_premises_to_lean_ir(
        &self,
        infer_result: &InferResult,
    ) -> Result<Vec<FactToLeanIR>, RuntimeError> {
        let mut seen = HashSet::new();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            if output.inferred_fact_ids.len() != output.inferred_facts.len() {
                return Err(to_lean_ir_error(
                    &output.itself_and_why_itself_is_stored.0.line_file(),
                    "inferred fact identity list does not match inferred facts",
                ));
            }
            let source_fact = &output.itself_and_why_itself_is_stored.0;
            let Some(source_fact_id) = output.fact_id else {
                continue;
            };
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                if !seen.insert(fact.to_string()) {
                    continue;
                }
                let proof = inferred_fact_proof_to_lean_ir(
                    source_fact,
                    Some(source_fact_id),
                    fact,
                    &output.itself_and_why_itself_is_stored.1,
                );
                if matches!(proof, FactProofToLeanIR::Inference { .. }) {
                    continue;
                }
                let fact_id = (*fact_id).ok_or_else(|| {
                    to_lean_ir_error(
                        &fact.line_file(),
                        "a supported forall inference reached To-Lean without a FactId",
                    )
                })?;
                inferred.push(FactToLeanIR {
                    fact_id: Some(fact_id),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }
}

fn inferred_fact_proof_to_lean_ir(
    source_fact: &Fact,
    source_fact_id: Option<FactId>,
    inferred_fact: &Fact,
    reason: &str,
) -> FactProofToLeanIR {
    if positive_real_membership_infers_strict_positivity(source_fact, inferred_fact) {
        if let Some(source_fact_id) = source_fact_id {
            return FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::PositiveRealMembership),
                parameter_requirements: Vec::new(),
                premises: vec![FactToLeanIR {
                    fact_id: Some(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: FactProofToLeanIR::KnownFactCitation { source_fact_id },
                }],
            };
        }
    }
    if crate::to_lean_ir::is_closed_numeric_relation(inferred_fact) {
        if let Some(carrier) =
            crate::to_lean_ir::closed_compact_numeric_set_fact_carrier(source_fact)
        {
            return FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::ClosedNumericReflection { carrier },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            };
        }
    }
    FactProofToLeanIR::Inference {
        source_fact_id,
        reason: reason.to_string(),
    }
}

fn positive_real_membership_infers_strict_positivity(
    source_fact: &Fact,
    inferred_fact: &Fact,
) -> bool {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = source_fact else {
        return false;
    };
    if !matches!(membership.set, Obj::StandardSet(StandardSet::RPos)) {
        return false;
    }
    let Fact::AtomicFact(order) = inferred_fact else {
        return false;
    };
    match order {
        AtomicFact::LessFact(fact) => {
            fact.left.to_string() == "0"
                && obj_equality_key(&fact.right) == obj_equality_key(&membership.element)
        }
        AtomicFact::GreaterFact(fact) => {
            fact.right.to_string() == "0"
                && obj_equality_key(&fact.left) == obj_equality_key(&membership.element)
        }
        _ => false,
    }
}

fn object_type_fact_for_to_lean(obj: Obj, param_type: &ParamType, line_file: LineFile) -> Fact {
    match param_type {
        ParamType::Set(_) => IsSetFact::new(obj, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(obj, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(obj, line_file).into(),
        ParamType::Obj(set) => InFact::new(obj, set.clone(), line_file).into(),
    }
}

fn stored_fact_id_from_infer_result(
    infer_result: &InferResult,
    expected: &Fact,
    context: &str,
) -> Result<FactId, RuntimeError> {
    infer_result
        .store_fact_outputs
        .iter()
        .find(|output| output.itself_and_why_itself_is_stored.0.to_string() == expected.to_string())
        .and_then(|output| output.fact_id)
        .ok_or_else(|| {
            to_lean_ir_error(
                &expected.line_file(),
                format!(
                    "{} `{}` reached To-Lean without a FactId",
                    context, expected
                ),
            )
        })
}

fn contradiction_results_to_lean_ir(
    runtime: &Runtime,
    results: &[StmtResult],
    impossible_fact: &AtomicFact,
    context: &ToLeanIrContext,
) -> Result<ContradictionToLeanIR, RuntimeError> {
    if results.len() != 2 {
        return Err(to_lean_ir_error(
            &impossible_fact.line_file(),
            "a contradiction must retain exactly the named fact and its logical negation",
        ));
    }
    let expected_fact: Fact = impossible_fact.clone().into();
    let expected_negation: Fact = impossible_fact.logical_negation()?.into();
    let mut fact = runtime.fact_to_lean_ir_from_result(&results[0], "impossible fact", context)?;
    let mut negated_fact =
        runtime.fact_to_lean_ir_from_result(&results[1], "negated impossible fact", context)?;
    if fact.proposition.to_string() != expected_fact.to_string()
        || negated_fact.proposition.to_string() != expected_negation.to_string()
    {
        return Err(to_lean_ir_error(
            &impossible_fact.line_file(),
            "retained contradiction checks do not match the named impossible fact",
        ));
    }
    fact.fact_id = None;
    negated_fact.fact_id = None;
    Ok(ContradictionToLeanIR {
        fact: Box::new(fact),
        negated_fact: Box::new(negated_fact),
    })
}

fn param_group_to_lean_ir(
    group: &ParamGroupWithParamType,
) -> Result<ParamGroupToLeanIR, RuntimeError> {
    let Some(anchor) = group.params.first().map(|binding| binding.id()) else {
        return Err(to_lean_ir_error(
            &default_line_file(),
            "To-Lean cannot lower an empty parameter group",
        ));
    };
    Ok(ParamGroupToLeanIR {
        symbol_ids: group.params.iter().map(|binding| binding.id()).collect(),
        names: group
            .params
            .iter()
            .map(|binding| binding.name().to_string())
            .collect(),
        param_type: param_type_to_lean_ir(&group.param_type, anchor)?,
    })
}

fn param_type_to_lean_ir(
    param_type: &ParamType,
    generic_anchor: SymbolId,
) -> Result<ParamTypeToLeanIR, RuntimeError> {
    let generic_element_carrier = || LeanCarrierToLeanIR::Generic {
        anchor: generic_anchor,
    };
    match param_type {
        ParamType::Set(_) => Ok(ParamTypeToLeanIR::Set {
            element_carrier: generic_element_carrier(),
        }),
        ParamType::NonemptySet(_) => Ok(ParamTypeToLeanIR::NonemptySet {
            element_carrier: generic_element_carrier(),
        }),
        ParamType::FiniteSet(_) => Ok(ParamTypeToLeanIR::FiniteSet {
            element_carrier: generic_element_carrier(),
        }),
        ParamType::Obj(obj) => {
            let set = ObjToLeanIR::lower(obj)
                .map_err(|message| to_lean_ir_error(&default_line_file(), message))?;
            let element_carrier = LeanCarrierToLeanIR::for_membership_set(&set);
            Ok(ParamTypeToLeanIR::MemberOf {
                set,
                element_carrier,
            })
        }
    }
}

fn facts_align_by_rational_normalization(source: &Fact, goal: &Fact) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(goal)) = (source, goal) else {
        return false;
    };
    if source.key() != goal.key() || source.is_true() != goal.is_true() {
        return false;
    }
    let source_args = source.args_ref();
    let goal_args = goal.args_ref();
    source_args.len() == goal_args.len()
        && source_args
            .iter()
            .zip(goal_args.iter())
            .all(|(source, goal)| objs_align_by_nested_rational_normalization(source, goal))
}

fn objs_align_by_nested_rational_normalization(source: &Obj, goal: &Obj) -> bool {
    if objs_equal_by_rational_expression_evaluation(source, goal) {
        return true;
    }
    let result: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        goal,
        &mut |source_arg, goal_arg| {
            Ok(objs_align_by_nested_rational_normalization(
                source_arg, goal_arg,
            ))
        },
    );
    result.unwrap_or(false)
}

fn ensure_fact_objects_lower_to_lean_ir(fact: &Fact) -> Result<(), RuntimeError> {
    let mut objects = Vec::new();
    collect_fact_objects_for_to_lean(fact, &mut objects);
    for object in objects {
        ObjToLeanIR::lower(object)
            .map_err(|message| to_lean_ir_error(&fact.line_file(), message))?;
    }
    Ok(())
}

fn collect_fact_objects_for_to_lean<'a>(fact: &'a Fact, objects: &mut Vec<&'a Obj>) {
    match fact {
        Fact::AtomicFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ForallFact(fact) => collect_forall_objects_for_to_lean(fact, objects),
        Fact::ForallFactWithIff(fact) => {
            collect_forall_objects_for_to_lean(&fact.forall_fact, objects);
            for iff_fact in fact.iff_facts.iter() {
                collect_forall_conclusion_objects_for_to_lean(iff_fact, objects);
            }
        }
        Fact::NotForall(fact) => collect_forall_objects_for_to_lean(&fact.forall_fact, objects),
    }
}

fn collect_forall_objects_for_to_lean<'a>(fact: &'a ForallFact, objects: &mut Vec<&'a Obj>) {
    for group in fact.params_def_with_type.groups.iter() {
        if let ParamType::Obj(set) = &group.param_type {
            objects.push(set);
        }
    }
    for premise in fact.dom_facts.iter() {
        collect_fact_objects_for_to_lean(premise, objects);
    }
    for conclusion in fact.then_facts.iter() {
        collect_forall_conclusion_objects_for_to_lean(conclusion, objects);
    }
}

fn collect_forall_conclusion_objects_for_to_lean<'a>(
    fact: &'a ExistOrAndChainAtomicFact,
    objects: &mut Vec<&'a Obj>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(fact) => {
            objects.extend(fact.get_args_from_fact_ref())
        }
        ExistOrAndChainAtomicFact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
    }
}

fn param_types_match_for_projection(left: &ParamType, right: &ParamType) -> bool {
    match (left, right) {
        (ParamType::Set(_), ParamType::Set(_))
        | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
        | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => true,
        (ParamType::Obj(left), ParamType::Obj(right)) => {
            obj_equality_key(left) == obj_equality_key(right)
        }
        _ => false,
    }
}

fn fact_uses_only_forall_params(fact: &FactToLeanIR, retained_names: &HashSet<String>) -> bool {
    let mut objects = Vec::new();
    collect_fact_objects_for_to_lean(&fact.proposition, &mut objects);
    objects
        .into_iter()
        .flat_map(Obj::collect_forall_free_param_names)
        .all(|name| retained_names.contains(&name))
}

fn to_lean_ir_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}
