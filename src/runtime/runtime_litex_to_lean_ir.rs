use crate::litex_to_lean_ir::{
    LitexToLeanRegisteredRuleApplicationIr, LitexToLeanTypedBoundObjectIr,
};
use crate::prelude::*;
use crate::verify::local_builtin_catalog::registered_local_builtin_rules;
use crate::verify::rule_schema::{
    canonical_atomic_facts_equal, canonical_objs_equal, match_conclusion, MatchLimits,
};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
struct LitexToLeanIrConstructionContext {
    local_fact_ids: HashMap<String, FactId>,
}

impl LitexToLeanIrConstructionContext {
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
    pub(crate) fn build_litex_to_lean_ir_statement(
        &self,
        result: &StmtResult,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        if let Some(success) = result.factual_success() {
            ensure_fact_objects_supported_by_litex_to_lean_ir(&success.stmt)?;
            let fact = self.build_litex_to_lean_ir_fact_from_success(success)?;
            let well_definedness_context =
                self.well_definedness_context_for_factual_success(success);
            let excluded = HashSet::from([success.stmt.to_string()]);
            if success.fact_id.is_none() {
                return self
                    .build_litex_to_lean_ir_projected_forall_statement(success, fact, excluded);
            }
            return Ok(LitexToLeanStatementIr::Fact(LitexToLeanFactStatementIr {
                fact,
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &success.well_definedness,
                    &well_definedness_context,
                )?,
            }));
        }

        let Some(success) = result.non_factual_success() else {
            return Err(litex_to_lean_ir_error(
                &result.line_file(),
                "Litex-to-Lean IR requires a successful statement result",
            ));
        };
        match &success.stmt {
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(stmt)) => Ok(
                LitexToLeanStatementIr::AbstractProp(LitexToLeanAbstractPropIr {
                    name: stmt.name.clone(),
                    params: stmt.params.clone(),
                }),
            ),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(stmt)) => {
                for fact in stmt.iff_facts.iter() {
                    ensure_fact_objects_supported_by_litex_to_lean_ir(fact)?;
                }
                Ok(LitexToLeanStatementIr::Prop(LitexToLeanPropIr {
                    name: stmt.name.clone(),
                    params: stmt
                        .params_def_with_type
                        .groups
                        .iter()
                        .map(build_litex_to_lean_ir_parameter_group)
                        .collect::<Result<Vec<_>, RuntimeError>>()?,
                    iff_facts: stmt.iff_facts.clone(),
                }))
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(stmt)) => {
                self.build_litex_to_lean_ir_have_object_equal_statement(stmt, success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(stmt)) => {
                self.build_litex_to_lean_ir_have_function_equal_statement(stmt, success)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(stmt)) => {
                self.build_litex_to_lean_ir_have_object_choice_statement(stmt, success)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromExistFact(stmt)) => self
                .build_litex_to_lean_ir_existential_witness(
                    &stmt.equal_tos,
                    &stmt.line_file,
                    success,
                ),
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromAtomicFact(stmt)) => self
                .build_litex_to_lean_ir_existential_witness(
                    &stmt.equal_tos,
                    &stmt.line_file,
                    success,
                ),
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromThm(stmt)) => Err(
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "Litex-to-Lean does not yet support theorem-backed `obtain`; use an explicit theorem application followed by existential elimination",
                ),
            ),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(stmt)) => self
                .build_litex_to_lean_ir_existential_witness(
                    &stmt.param_def.collect_param_bindings(),
                    &stmt.line_file,
                    success,
                ),
            Stmt::Witness(WitnessStmt::WitnessExistFact(stmt)) => {
                self.build_litex_to_lean_ir_witness_exist_statement(stmt, success)
            }
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(stmt)) => {
                self.build_litex_to_lean_ir_witness_atomic_fact_statement(stmt, success)
            }
            Stmt::By(ByStmt::ByCasesStmt(stmt)) => {
                self.build_litex_to_lean_ir_by_cases_statement(stmt, success)
            }
            Stmt::By(ByStmt::ByContraStmt(stmt)) => {
                self.build_litex_to_lean_ir_by_contra_statement(stmt, success)
            }
            Stmt::By(ByStmt::ByDefStmt(stmt)) => {
                self.build_litex_to_lean_ir_by_definition_statement(stmt, success)
            }
            Stmt::DefThmStmt(stmt) => {
                self.build_litex_to_lean_ir_named_theorem_statement(stmt, success)
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(stmt)) => {
                let excluded = stmt
                    .facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<HashSet<_>>();
                let mut facts = Vec::with_capacity(stmt.facts.len());
                for fact in stmt.facts.iter() {
                    ensure_fact_objects_supported_by_litex_to_lean_ir(fact)?;
                    facts.push(LitexToLeanFactIr {
                        fact_id: self.known_fact_id_for_fact(fact)?,
                        proposition: fact.clone(),
                        proof: LitexToLeanFactProofIr::Trusted,
                    });
                }
                Ok(LitexToLeanStatementIr::Trust(LitexToLeanTrustIr {
                    facts,
                    inferred_facts: self
                        .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                }))
            }
            other => Err(litex_to_lean_ir_error(
                &other.line_file(),
                format!(
                    "Litex-to-Lean IR MVP does not support statement kind `{}`",
                    other.stmt_type_name()
                ),
            )),
        }
    }

    fn build_litex_to_lean_ir_have_function_equal_statement(
        &self,
        stmt: &HaveFnEqualStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = success.function_definition_verification.as_ref() else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition has no structured body-to-environment verification result",
            ));
        };
        if success.inside_results.len() != 1 || verification.return_check_index != 0 {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition must retain exactly one mapped return-membership proof",
            ));
        }
        let source_return_set = stmt.equal_to_anonymous_fn.body.ret_set.as_ref().clone();

        let function_set = FnSet::from_body(stmt.equal_to_anonymous_fn.body.clone())?;
        let source_function_set: Obj = function_set.clone().into();
        let function = LitexToLeanFunctionTypeIr::lower(&function_set)
            .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let source_body = stmt.equal_to_anonymous_fn.equal_to.as_ref().clone();
        let body = LitexToLeanObjectIr::lower(&source_body)
            .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;

        let mut expected_parameter_facts = Vec::new();
        for group in stmt.equal_to_anonymous_fn.body.params_def_with_set.iter() {
            expected_parameter_facts.extend(
                group
                    .facts_for_binding_scope(ParamObjType::FnSet)
                    .into_iter(),
            );
        }
        let expected_domain_facts = stmt
            .equal_to_anonymous_fn
            .body
            .dom_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let mut used_assumption_outputs = HashSet::new();
        let mut lower_local_premises = |expected: &[Fact], role: &str| {
            let mut premises = Vec::with_capacity(expected.len());
            for fact in expected {
                let (index, output) = verification
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .enumerate()
                    .find(|(_, output)| {
                        output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string()
                    })
                    .ok_or_else(|| {
                        litex_to_lean_ir_error(
                            &stmt.line_file,
                            format!("function definition is missing its retained {role} `{fact}`"),
                        )
                    })?;
                if !used_assumption_outputs.insert(index) {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "function definition reuses one retained assumption for multiple binder roles",
                    ));
                }
                let fact_id = output.fact_id.ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &stmt.line_file,
                        format!("function definition {role} `{fact}` has no temporary FactId"),
                    )
                })?;
                premises.push(LitexToLeanLocalPremiseIr::new(fact_id, fact.clone()));
            }
            Ok::<Vec<LitexToLeanLocalPremiseIr>, RuntimeError>(premises)
        };
        let parameter_premises =
            lower_local_premises(&expected_parameter_facts, "parameter premise")?;
        let domain_premises = lower_local_premises(&expected_domain_facts, "domain premise")?;
        if used_assumption_outputs.len() != verification.assumption_infers.store_fact_outputs.len()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition retained assumption effects outside its parameter/domain contract",
            ));
        }
        let inferred_premises = self
            .build_litex_to_lean_ir_supported_inferred_premises(&verification.assumption_infers)?;
        // Inference may derive additional facts from a parameter/domain
        // assumption that the selected return proof never uses.  Emit only
        // the inferred premises with checked adapters; if the retained return
        // proof cites any omitted inference, its unresolved FactId still makes
        // construction/emission fail closed.

        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            source_return_set.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let assumption_context = LitexToLeanIrConstructionContext::default()
            .with_infer_result(&verification.assumption_infers);
        let mut return_check = self.build_litex_to_lean_ir_fact_from_result(
            &success.inside_results[verification.return_check_index],
            "function definition return-membership proof",
            &assumption_context,
        )?;
        if return_check.proposition.to_string() != expected_return_check.to_string() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                format!(
                    "function definition return check `{}` does not match expected `{}`",
                    return_check.proposition, expected_return_check
                ),
            ));
        }
        return_check.fact_id = None;

        let function_identifier_obj = self.declared_identifier_obj(stmt.name());
        let expected_membership: Fact = InFact::new(
            function_identifier_obj.clone(),
            source_function_set.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let expected_equality: Fact = EqualFact::new(
            function_identifier_obj,
            stmt.equal_to_anonymous_fn.clone().into(),
            stmt.line_file.clone(),
        )
        .into();
        if verification.function_membership.to_string() != expected_membership.to_string()
            || verification.defining_equality.to_string() != expected_equality.to_string()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition stored effects do not match its checked signature and body",
            ));
        }
        if success.infers.store_fact_outputs.len() != 2
            || success
                .infers
                .store_fact_outputs
                .iter()
                .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition stored effects exceed the membership/equality contract of this Litex-to-Lean slice",
            ));
        }
        let membership_id = stored_fact_id_from_infer_result(
            &success.infers,
            &expected_membership,
            "function membership",
        )?;
        let equality_id = stored_fact_id_from_infer_result(
            &success.infers,
            &expected_equality,
            "function defining equality",
        )?;

        Ok(LitexToLeanStatementIr::HaveFnEqual(
            LitexToLeanHaveFunctionEqualIr {
                symbol_id: stmt.symbol_binding.id(),
                name: stmt.name().to_string(),
                function,
                source_function_set,
                body,
                source_body,
                source_return_set,
                parameter_premises,
                domain_premises,
                inferred_premises,
                return_check,
                membership: LitexToLeanStoredFunctionFactIr {
                    fact_id: membership_id,
                    proposition: expected_membership.clone(),
                    expected_proposition: expected_membership,
                },
                defining_equality: LitexToLeanStoredFunctionFactIr {
                    fact_id: equality_id,
                    proposition: expected_equality.clone(),
                    expected_proposition: expected_equality,
                },
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &success.well_definedness,
                    &assumption_context,
                )?,
            },
        ))
    }

    fn build_litex_to_lean_ir_witness_exist_statement(
        &self,
        stmt: &WitnessExistFact,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = success.witness_exist_verification.as_ref() else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "existential witness has no structured introduction verification result",
            ));
        };
        if success
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty())
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "existential witness inferred consequences are not represented by this Litex-to-Lean tranche",
            ));
        }

        let existential: Fact = stmt.exist_fact_in_witness.clone().into();
        if success.infers.store_fact_outputs.len() != 1
            || success.infers.store_fact_outputs[0]
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != existential.to_string()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "existential witness stored facts do not match its introduced existential",
            ));
        }
        let fact_id = stored_fact_id_from_infer_result(
            &success.infers,
            &existential,
            "existential witness fact",
        )?;
        let fact = self.build_litex_to_lean_ir_exist_introduction_fact(
            stmt,
            verification,
            &success.inside_results,
            Some(fact_id),
        )?;

        Ok(LitexToLeanStatementIr::Proof(LitexToLeanProofStatementIr {
            facts: vec![fact],
            inferred_facts: Vec::new(),
        }))
    }

    fn build_litex_to_lean_ir_exist_introduction_fact(
        &self,
        stmt: &WitnessExistFact,
        verification: &WitnessExistVerificationResult,
        inside_results: &[StmtResult],
        fact_id: Option<FactId>,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        if !stmt.exist_fact_in_witness.is_plain_exist() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "the current Litex-to-Lean witness tranche supports positive `exist`, not `exist!` or `not exist`",
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
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "existential witness evidence has inconsistent parameter, proof-step, body, or uniqueness mappings",
            ));
        }

        let existential: Fact = stmt.exist_fact_in_witness.clone().into();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&existential)?;

        let proof_steps = inside_results
            .get(..verification.proof_step_count)
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "existential witness proof-step range points outside retained results",
                )
            })?
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
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
            LitexToLeanObjectIr::lower(witness)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
            if matches!(param_type, ParamType::Set(_)) {
                if check_result.is_some() {
                    return Err(litex_to_lean_ir_error(
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
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "existential witness parameter {} is missing its checked type requirement",
                        index + 1
                    ),
                ));
            };
            let expected = object_type_fact_for_litex_to_lean(
                witness.clone(),
                param_type,
                stmt.line_file.clone(),
            );
            let mut requirement = self.build_litex_to_lean_ir_fact_from_result(
                check_result.as_ref(),
                "existential witness parameter requirement",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            if requirement.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
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
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "existential witness reuses a retained result for multiple evidence roles",
                ));
            }
            let expected = self
                .inst_quantifier_free_fact(body, &param_to_obj_map, ParamObjType::Exist, None)?
                .to_fact();
            let mut premise = self.build_litex_to_lean_ir_fact_from_result(
                inside_results.get(*result_index).ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &stmt.line_file,
                        "existential witness body-check index points outside retained results",
                    )
                })?,
                "existential witness body requirement",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            if premise.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
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
        if used_result_indices.len() != inside_results.len() {
            return Err(litex_to_lean_ir_error(
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

        Ok(LitexToLeanFactIr {
            fact_id,
            proposition: existential,
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ExistIntroduction {
                    witnesses: stmt.equal_tos.clone(),
                    steps: proof_steps,
                    expected_parameter_requirements,
                    expected_body_facts,
                },
                parameter_requirements,
                premises: body_premises,
            },
        })
    }

    fn build_litex_to_lean_ir_witness_atomic_fact_statement(
        &self,
        stmt: &WitnessAtomicFact,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = success.witness_atomic_fact_verification.as_ref() else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness has no frozen definition-introduction verification result",
            ));
        };
        if verification.definition_parameter_check.is_unknown() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness retained an unsuccessful definition-parameter check",
            ));
        }

        let predicate_name = stmt.atomic_fact.predicate.to_string();
        let local_predicate_name = predicate_name
            .rsplit_once(MOD_SIGN)
            .map(|(_, local_name)| local_name)
            .unwrap_or(predicate_name.as_str());
        if verification.definition.name != local_predicate_name {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness certificate names a different proposition definition",
            ));
        }
        if verification.definition.iff_facts.len() != 1 {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness certificate must retain exactly one definition clause",
            ));
        }
        let Fact::ExistFact(definition_existential) = &verification.definition.iff_facts[0] else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness certificate must retain a plain existential definition clause",
            ));
        };
        if !definition_existential.is_plain_exist()
            || !verification.instantiated_existential.is_plain_exist()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness currently supports positive `exist`, not `exist!` or `not exist`",
            ));
        }

        let reconstructed = self.instantiate_existential_prop_definition(
            &stmt.atomic_fact,
            &verification.definition,
            &stmt.line_file,
        )?;
        if !reconstructed.is_plain_exist()
            || Runtime::exist_fact_normalized_body_string(self, &reconstructed)?
                != Runtime::exist_fact_normalized_body_string(
                    self,
                    &verification.instantiated_existential,
                )?
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness certificate does not match the retained instantiated definition",
            ));
        }

        let target: Fact = stmt.atomic_fact.clone().into();
        let existential: Fact = verification.instantiated_existential.clone().into();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&target)?;
        ensure_fact_objects_supported_by_litex_to_lean_ir(&existential)?;
        let target_id =
            stored_fact_id_from_infer_result(&success.infers, &target, "atomic fact witness")?;
        let existential_id = added_fact_id_from_infer_result(
            &success.infers,
            &existential,
            "atomic fact witness definition consequence",
        )?;

        let expanded = WitnessExistFact::new(
            stmt.witnesses.clone(),
            verification.instantiated_existential.clone(),
            stmt.proof.clone(),
            stmt.line_file.clone(),
        );
        let existential_introduction = self.build_litex_to_lean_ir_exist_introduction_fact(
            &expanded,
            &verification.witness_verification,
            &success.inside_results,
            None,
        )?;
        let named_fact = LitexToLeanFactIr {
            fact_id: Some(target_id),
            proposition: target.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DefinitionIntroduction {
                    definition: verification.definition.name.clone(),
                    expected_source: existential.clone(),
                    expected_target: target.clone(),
                },
                parameter_requirements: Vec::new(),
                premises: vec![existential_introduction],
            },
        };
        let projected_existential = LitexToLeanFactIr {
            fact_id: Some(existential_id),
            proposition: existential.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DefinitionProjection {
                    definition: verification.definition.name.clone(),
                    expected_source: target.clone(),
                    expected_target: existential.clone(),
                },
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    fact_id: Some(target_id),
                    proposition: target.clone(),
                    proof: LitexToLeanFactProofIr::KnownFactCitation {
                        source_fact_id: target_id,
                    },
                }],
            },
        };

        let excluded = HashSet::from([target.to_string(), existential.to_string()]);
        let mut inferred_facts = vec![projected_existential];
        inferred_facts
            .extend(self.build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?);
        Ok(LitexToLeanStatementIr::Proof(LitexToLeanProofStatementIr {
            facts: vec![named_fact],
            inferred_facts,
        }))
    }

    fn build_litex_to_lean_ir_existential_witness(
        &self,
        bindings: &[SymbolBinding],
        line_file: &LineFile,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = success.existential_elimination_verification.as_ref() else {
            return Err(litex_to_lean_ir_error(
                line_file,
                "existential elimination has no structured source-to-projection verification result",
            ));
        };
        let exist_fact = &verification.source_exist_fact;
        if !exist_fact.is_plain_exist() || verification.includes_uniqueness {
            return Err(litex_to_lean_ir_error(
                line_file,
                "the current Litex-to-Lean elimination tranche supports positive `exist`, not `exist!` or `not exist`",
            ));
        }
        if bindings.is_empty()
            || bindings.len() != exist_fact.params_def_with_type().number_of_params()
            || bindings.len() != verification.witness_type_facts.len()
            || exist_fact.facts().len() != verification.instantiated_body_facts.len()
        {
            return Err(litex_to_lean_ir_error(
                line_file,
                "existential elimination evidence has inconsistent witness, type-fact, or body-fact mappings",
            ));
        }
        if success.inside_results.len() != 1 || verification.source_result_index != 0 {
            return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
                line_file,
                "existential elimination inferred consequences are not represented by this Litex-to-Lean tranche",
            ));
        }

        let mut source = self.build_litex_to_lean_ir_fact_from_result(
            &success.inside_results[verification.source_result_index],
            "existential elimination source proof",
            &LitexToLeanIrConstructionContext::default(),
        )?;
        let source_proposition = source.proposition.clone();
        let Fact::ExistFact(source_exist_fact) = &source_proposition else {
            return Err(litex_to_lean_ir_error(
                line_file,
                "existential elimination source proof does not certify an `exist` fact",
            ));
        };
        if !source_exist_fact.is_plain_exist()
            || Runtime::exist_fact_normalized_body_string(self, source_exist_fact)?
                != Runtime::exist_fact_normalized_body_string(self, exist_fact)?
        {
            return Err(litex_to_lean_ir_error(
                line_file,
                format!(
                    "existential elimination source `{}` does not certify `{}`",
                    source.proposition,
                    Fact::from(exist_fact.clone())
                ),
            ));
        }
        let source_exist_fact = source_exist_fact.clone();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&source_proposition)?;
        source.fact_id = None;

        let witness_objs = bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect::<Vec<Obj>>();
        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            source_exist_fact.params_def_with_type(),
            &witness_objs,
            ParamObjType::Exist,
        )?;
        let flat_types = source_exist_fact
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
            let calculated = object_type_fact_for_litex_to_lean(
                witness_objs[witness_index].clone(),
                param_type,
                line_file.clone(),
            );
            if calculated.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
                    line_file,
                    format!(
                        "existential elimination stored type fact `{}` does not match expected `{}`",
                        expected, calculated
                    ),
                ));
            }
            ensure_fact_objects_supported_by_litex_to_lean_ir(expected)?;
            let fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                expected,
                "existential elimination witness type fact",
            )?;
            if !expected_fact_keys.insert(expected.to_string()) {
                return Err(litex_to_lean_ir_error(
                    line_file,
                    "existential elimination emitted duplicate projection facts",
                ));
            }
            witnesses.push(LitexToLeanExistentialWitnessIr {
                symbol_id: binding.id(),
                name: binding.name().to_string(),
                param_type: build_litex_to_lean_ir_parameter_type(param_type)?,
            });
            projections.push(LitexToLeanFactIr {
                fact_id: Some(fact_id),
                proposition: expected.clone(),
                proof: LitexToLeanFactProofIr::ExistentialElimination {
                    source_proposition: source_proposition.clone(),
                    role: LitexToLeanExistentialProjectionRoleIr::ParameterType { witness_index },
                    expected_proposition: expected.clone(),
                },
            });
        }

        let param_to_obj_map = source_exist_fact
            .params_def_with_type()
            .param_defs_and_args_to_param_to_arg_map(&witness_objs);
        for (body_index, (body, expected)) in source_exist_fact
            .facts()
            .iter()
            .zip(verification.instantiated_body_facts.iter())
            .enumerate()
        {
            let calculated = self
                .inst_quantifier_free_fact(body, &param_to_obj_map, ParamObjType::Exist, None)?
                .to_fact();
            if calculated.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
                    line_file,
                    format!(
                        "existential elimination stored body fact `{}` does not match expected `{}`",
                        expected, calculated
                    ),
                ));
            }
            ensure_fact_objects_supported_by_litex_to_lean_ir(expected)?;
            let fact_id = stored_fact_id_from_infer_result(
                &success.infers,
                expected,
                "existential elimination body fact",
            )?;
            if !expected_fact_keys.insert(expected.to_string()) {
                return Err(litex_to_lean_ir_error(
                    line_file,
                    "existential elimination emitted duplicate projection facts",
                ));
            }
            projections.push(LitexToLeanFactIr {
                fact_id: Some(fact_id),
                proposition: expected.clone(),
                proof: LitexToLeanFactProofIr::ExistentialElimination {
                    source_proposition: source_proposition.clone(),
                    role: LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index },
                    expected_proposition: expected.clone(),
                },
            });
        }

        if success.infers.store_fact_outputs.len() != expected_fact_keys.len()
            || success.infers.store_fact_outputs.iter().any(|output| {
                !expected_fact_keys.contains(&output.itself_and_why_itself_is_stored.0.to_string())
            })
        {
            return Err(litex_to_lean_ir_error(
                line_file,
                "existential elimination stored facts do not match its type-and-body projection contract",
            ));
        }

        Ok(LitexToLeanStatementIr::HaveExistentialWitness(
            LitexToLeanHaveExistentialWitnessIr {
                source,
                witnesses,
                projections,
            },
        ))
    }

    fn build_litex_to_lean_ir_have_object_choice_statement(
        &self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = success.object_choice_verification.as_ref() else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object choice has no structured nonemptiness-to-membership verification result",
            ));
        };
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if bindings_with_types.len() != verification.selected_type_facts.len()
            || bindings_with_types.len() != verification.nonempty_check_indices.len()
        {
            return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object choice inferred consequences are not represented by this Litex-to-Lean tranche",
            ));
        }

        let mut expected_fact_keys = HashSet::new();
        let mut choices = Vec::with_capacity(bindings_with_types.len());
        for (index, (binding, param_type)) in bindings_with_types.iter().enumerate() {
            let ParamType::Obj(carrier) = param_type else {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "object choice from meta-level parameter type `{}` has no checked inhabited-type backend",
                        param_type
                    ),
                ));
            };
            let Some(check_index) = verification.nonempty_check_indices[index] else {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "object-carrier choice did not retain a nonemptiness proof index",
                ));
            };
            let Some(check_result) = success.inside_results.get(check_index) else {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "object-carrier choice points outside its retained nonemptiness proofs",
                ));
            };
            let expected_nonempty: Fact =
                IsNonemptySetFact::new(carrier.clone(), stmt.line_file.clone()).into();
            let mut nonempty_proof = self.build_litex_to_lean_ir_fact_from_result(
                check_result,
                "object-choice nonemptiness proof",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            if nonempty_proof.proposition.to_string() != expected_nonempty.to_string() {
                return Err(litex_to_lean_ir_error(
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
                object_type_fact_for_litex_to_lean(defined_obj, param_type, stmt.line_file.clone());
            let selected_type_fact = &verification.selected_type_facts[index];
            if selected_type_fact.to_string() != expected_membership.to_string() {
                return Err(litex_to_lean_ir_error(
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
            let carrier_ir = LitexToLeanObjectIr::lower(carrier)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
            choices.push(LitexToLeanObjectChoiceIr {
                symbol_id: binding.id(),
                name: definition_name.clone(),
                carrier: carrier_ir.clone(),
                nonempty_proof,
                membership: LitexToLeanFactIr {
                    fact_id: Some(membership_fact_id),
                    proposition: selected_type_fact.clone(),
                    proof: LitexToLeanFactProofIr::ObjectChoice {
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
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object-choice stored facts do not match its selected membership contract",
            ));
        }

        Ok(LitexToLeanStatementIr::HaveObjChoice(
            LitexToLeanHaveObjectChoiceIr { choices },
        ))
    }

    fn build_litex_to_lean_ir_have_object_equal_statement(
        &self,
        stmt: &HaveObjEqualStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if bindings_with_types.len() != stmt.objs_equal_to.len()
            || bindings_with_types.len() != success.inside_results.len()
        {
            return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "have-object equality inferred consequences are not represented by this Litex-to-Lean tranche",
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
            let value_type_fact = object_type_fact_for_litex_to_lean(
                value.clone(),
                param_type,
                stmt.line_file.clone(),
            );
            let stored_type_fact = object_type_fact_for_litex_to_lean(
                defined_obj.clone(),
                param_type,
                stmt.line_file.clone(),
            );
            let stored_equality: Fact =
                EqualFact::new(defined_obj, value.clone(), stmt.line_file.clone()).into();

            let mut value_check = self.build_litex_to_lean_ir_fact_from_result(
                &success.inside_results[index],
                "have-object value type check",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            if value_check.proposition.to_string() != value_type_fact.to_string() {
                return Err(litex_to_lean_ir_error(
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

            let value_ir = LitexToLeanObjectIr::lower(value)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
            definitions.push(LitexToLeanObjectDefinitionIr {
                symbol_id: binding.id(),
                name: definition_name.clone(),
                param_type: build_litex_to_lean_ir_parameter_type(param_type)?,
                value: value_ir.clone(),
            });
            facts.push(LitexToLeanFactIr {
                fact_id: Some(stored_type_fact_id),
                proposition: stored_type_fact,
                proof: LitexToLeanFactProofIr::ObjectDefinition {
                    definition: definition_name.clone(),
                    value: value_ir.clone(),
                    value_check: Some(Box::new(value_check)),
                },
            });
            facts.push(LitexToLeanFactIr {
                fact_id: Some(stored_equality_fact_id),
                proposition: stored_equality,
                proof: LitexToLeanFactProofIr::ObjectDefinition {
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
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "have-object equality stored facts do not match its type and defining-equality contract",
            ));
        }

        Ok(LitexToLeanStatementIr::HaveObjEqual(
            LitexToLeanHaveObjectEqualIr { definitions, facts },
        ))
    }

    fn build_litex_to_lean_ir_by_definition_statement(
        &self,
        stmt: &ByDefStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(ByVerificationResult::Definition(verification)) = success.by_verification.as_ref()
        else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-definition statement has no structured verification result",
            ));
        };
        if !verification.concrete_user_prop {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "Litex-to-Lean first statement tranche supports user `prop` reduction, not this builtin definition",
            ));
        }
        let definition = self
            .get_active_prop_definition_by_name(&verification.prop)
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "by-definition result no longer resolves its concrete prop definition",
                )
            })?;
        if definition.iff_facts.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "Litex-to-Lean rejects a bodyless concrete `prop`",
            ));
        }
        let target: Fact = stmt.fact.clone().into();
        if verification.stored_fact != target.to_string()
            || verification.definition_clause_facts.len() != definition.iff_facts.len()
            || success.inside_results.len() != verification.definition_clause_facts.len() + 1
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-definition retained statement, clause, or result counts do not match",
            ));
        }
        let parameter_wrapper = success
            .inside_results
            .first()
            .and_then(StmtResult::non_factual_success)
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "by-definition parameter checks were not retained as a grouped result",
                )
            })?;
        let proof = self.build_litex_to_lean_ir_definition_reduction(
            &target,
            &definition,
            &parameter_wrapper.inside_results,
            &verification.definition_clause_facts,
            &success.inside_results[1..],
            &LitexToLeanIrConstructionContext::default(),
        )?;
        let fact_id = stored_fact_id_from_infer_result(
            &success.infers,
            &target,
            "by-definition target fact",
        )?;
        let fact = LitexToLeanFactIr {
            fact_id: Some(fact_id),
            proposition: target.clone(),
            proof,
        };
        let excluded = HashSet::from([target.to_string()]);
        Ok(LitexToLeanStatementIr::Proof(LitexToLeanProofStatementIr {
            facts: vec![fact],
            inferred_facts: self
                .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
        }))
    }

    fn build_litex_to_lean_ir_by_cases_statement(
        &self,
        stmt: &ByCasesStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(ByVerificationResult::Cases(verification)) = success.by_verification.as_ref()
        else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-cases statement has no structured verification result",
            ));
        };
        if verification.cases.len() != verification.case_fact_ids.len()
            || verification.cases.len() != verification.case_result_counts.len()
            || verification.cases.len() != verification.proof_step_counts.len()
            || verification.cases.len() != verification.impossible_facts.len()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-cases verification has inconsistent branch metadata",
            ));
        }
        let Some(coverage_result) = success.inside_results.first() else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-cases verification did not retain its coverage proof",
            ));
        };
        let mut coverage = self.build_litex_to_lean_ir_fact_from_result(
            coverage_result,
            "by-cases coverage",
            &LitexToLeanIrConstructionContext::default(),
        )?;
        coverage.fact_id = None;
        let expected_coverage: Fact =
            OrFact::new(verification.cases.clone(), stmt.line_file.clone()).into();
        if coverage.proposition.to_string() != expected_coverage.to_string() {
            return Err(litex_to_lean_ir_error(
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
                litex_to_lean_ir_error(&stmt.line_file, "by-cases result count overflow")
            })?;
            if end > success.inside_results.len() {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "by-cases branch result count exceeds retained results",
                ));
            }
            case_slices.push(&success.inside_results[cursor..end]);
            cursor = end;
        }
        if cursor != success.inside_results.len() {
            return Err(litex_to_lean_ir_error(
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
            ensure_fact_objects_supported_by_litex_to_lean_ir(goal)?;
            let mut branches = Vec::with_capacity(verification.cases.len());
            for case_index in 0..verification.cases.len() {
                let case_fact: Fact = verification.cases[case_index].clone().into();
                let case_context = LitexToLeanIrConstructionContext {
                    local_fact_ids: HashMap::from([(
                        case_fact.to_string(),
                        verification.case_fact_ids[case_index],
                    )]),
                };
                let case_results = case_slices[case_index];
                let proof_step_count = verification.proof_step_counts[case_index];
                if proof_step_count > case_results.len() {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "by-cases proof-step count exceeds retained branch results",
                    ));
                }
                let steps = case_results[..proof_step_count]
                    .iter()
                    .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let remaining = &case_results[proof_step_count..];
                let exit = if verification.impossible_facts[case_index].is_some() {
                    if remaining.len() != 1 {
                        return Err(litex_to_lean_ir_error(
                            &stmt.line_file,
                            "an impossible by-cases branch must retain one contradiction result",
                        ));
                    }
                    LitexToLeanCaseBranchExitIr::Contradiction(
                        self.build_litex_to_lean_ir_wrapped_contradiction(
                            &remaining[0],
                            verification.impossible_facts[case_index]
                                .as_ref()
                                .expect("checked above"),
                            &case_context,
                        )?,
                    )
                } else {
                    if remaining.len() != verification.then_facts.len() {
                        return Err(litex_to_lean_ir_error(
                            &stmt.line_file,
                            "a by-cases branch does not retain one result per goal",
                        ));
                    }
                    let mut conclusion = self.build_litex_to_lean_ir_fact_from_result(
                        &remaining[goal_index],
                        "by-cases branch conclusion",
                        &case_context,
                    )?;
                    if conclusion.proposition.to_string() != goal.to_string() {
                        return Err(litex_to_lean_ir_error(
                            &stmt.line_file,
                            "by-cases branch conclusion does not match its exported goal",
                        ));
                    }
                    conclusion.fact_id = None;
                    LitexToLeanCaseBranchExitIr::Conclusion(conclusion)
                };
                branches.push(LitexToLeanCaseBranchIr {
                    assumption: LitexToLeanLocalPremiseIr::new(
                        verification.case_fact_ids[case_index],
                        case_fact,
                    ),
                    steps,
                    exit,
                });
            }

            facts.push(LitexToLeanFactIr {
                fact_id: Some(stored_fact_id_from_infer_result(
                    &success.infers,
                    goal,
                    "by-cases exported goal",
                )?),
                proposition: goal.clone(),
                proof: LitexToLeanFactProofIr::CaseSplit {
                    coverage: Box::new(coverage.clone()),
                    branches,
                },
            });
        }

        Ok(LitexToLeanStatementIr::Proof(LitexToLeanProofStatementIr {
            facts,
            inferred_facts: self
                .build_litex_to_lean_ir_inferred_facts(&success.infers, &explicit_keys)?,
        }))
    }

    fn build_litex_to_lean_ir_by_contra_statement(
        &self,
        stmt: &ByContraStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(ByVerificationResult::Contra(verification)) = success.by_verification.as_ref()
        else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-contra statement has no structured verification result",
            ));
        };
        if verification.to_prove.to_string() != stmt.to_prove.to_string() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-contra verification target does not match the statement target",
            ));
        }
        if verification.proof_step_count + 2 != success.inside_results.len() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-contra must retain its proof steps and two contradiction checks",
            ));
        }
        let reverse_context = LitexToLeanIrConstructionContext {
            local_fact_ids: HashMap::from([(
                verification.reverse_assumption.to_string(),
                verification.reverse_assumption_fact_id,
            )]),
        };
        let steps = success.inside_results[..verification.proof_step_count]
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let contradiction = build_litex_to_lean_ir_contradiction_results(
            self,
            &success.inside_results[verification.proof_step_count..],
            &verification.impossible_fact,
            &reverse_context,
        )?;
        let explicit_keys = HashSet::from([stmt.to_prove.to_string()]);
        let fact = LitexToLeanFactIr {
            fact_id: Some(stored_fact_id_from_infer_result(
                &success.infers,
                &stmt.to_prove,
                "by-contra exported goal",
            )?),
            proposition: stmt.to_prove.clone(),
            proof: LitexToLeanFactProofIr::ByContradiction {
                reverse_assumption: LitexToLeanLocalPremiseIr::new(
                    verification.reverse_assumption_fact_id,
                    verification.reverse_assumption.clone(),
                ),
                steps,
                contradiction,
            },
        };

        Ok(LitexToLeanStatementIr::Proof(LitexToLeanProofStatementIr {
            facts: vec![fact],
            inferred_facts: self
                .build_litex_to_lean_ir_inferred_facts(&success.infers, &explicit_keys)?,
        }))
    }

    fn build_litex_to_lean_ir_nested_statement(
        &self,
        result: &StmtResult,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        match result.litex_to_lean_ir() {
            Some(ir) => Ok(ir.clone()),
            None => self.build_litex_to_lean_ir_statement(result),
        }
    }

    fn build_litex_to_lean_ir_named_theorem_statement(
        &self,
        stmt: &DefThmStmt,
        success: &NonFactualStmtSuccess,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        if stmt.is_axiom() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "Litex-to-Lean does not compile explicit `axiom` declarations",
            ));
        }
        let verification = success.theorem_verification.as_ref().ok_or_else(|| {
            litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified theorem reached Litex-to-Lean without theorem proof-scope evidence",
            )
        })?;
        if verification.name != stmt.name
            || verification.forall_fact.to_string() != stmt.forall_fact.to_string()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "theorem proof-scope evidence does not match the source declaration",
            ));
        }
        if verification.proof_step_count != stmt.prove_process.len()
            || success.inside_results.len()
                != verification.proof_step_count + verification.forall_fact.then_facts.len()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "theorem proof-scope results are missing or out of verifier order",
            ));
        }

        let proposition: Fact = verification.forall_fact.clone().into();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&proposition)?;
        let matching_outputs = success
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.itself_and_why_itself_is_stored.0.to_string() == proposition.to_string()
            })
            .collect::<Vec<_>>();
        if matching_outputs.len() != 1 {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "theorem environment effect does not contain exactly one complete source forall",
            ));
        }

        let parameter_reason = InferReason::ParameterDefinition.store_reason();
        let parameter_premises = verification
            .assumption_infers
            .store_fact_outputs
            .iter()
            .filter(|output| output.itself_and_why_itself_is_stored.1 == parameter_reason)
            .map(|output| {
                let fact = output.itself_and_why_itself_is_stored.0.clone();
                let fact_id = output.fact_id.ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &fact.line_file(),
                        "a theorem parameter premise reached Litex-to-Lean without a FactId",
                    )
                })?;
                Ok(LitexToLeanLocalPremiseIr::new(fact_id, fact))
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let mut premises = Vec::with_capacity(verification.forall_fact.dom_facts.len());
        for dom_fact in verification.forall_fact.dom_facts.iter() {
            let fact_id = verification
                .assumption_infers
                .store_fact_outputs
                .iter()
                .find(|output| {
                    output.itself_and_why_itself_is_stored.0.to_string() == dom_fact.to_string()
                })
                .and_then(|output| output.fact_id)
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &dom_fact.line_file(),
                        "a theorem domain premise reached Litex-to-Lean without a FactId",
                    )
                })?;
            premises.push(LitexToLeanLocalPremiseIr::new(fact_id, dom_fact.clone()));
        }
        let inferred_premises = self
            .build_litex_to_lean_ir_supported_inferred_premises(&verification.assumption_infers)?;
        let theorem_context = LitexToLeanIrConstructionContext::default()
            .with_infer_result(&verification.assumption_infers);
        let proof_steps = success.inside_results[..verification.proof_step_count]
            .iter()
            .enumerate()
            .map(|(index, result)| {
                Ok(LitexToLeanNamedTheoremProofStepIr {
                    position: index + 1,
                    statement: self.build_litex_to_lean_ir_nested_statement(result)?,
                })
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let mut conclusions = Vec::with_capacity(verification.forall_fact.then_facts.len());
        for result in success.inside_results[verification.proof_step_count..].iter() {
            conclusions.push(self.build_litex_to_lean_ir_fact_from_result(
                result,
                "theorem conclusion",
                &theorem_context,
            )?);
        }
        let theorem = LitexToLeanFactIr {
            fact_id: matching_outputs[0].fact_id,
            proposition: proposition.clone(),
            proof: LitexToLeanFactProofIr::ForallIntroduction {
                parameter_premises,
                premises,
                inferred_premises,
                conclusions,
            },
        };

        let mut excluded = HashSet::from([proposition.to_string()]);
        let stored_projections = self.build_litex_to_lean_ir_forall_projections(
            &success.infers,
            &theorem,
            &mut excluded,
        )?;
        if theorem.fact_id.is_none() && stored_projections.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified theorem had neither a complete FactId nor stored projections",
            ));
        }

        Ok(LitexToLeanStatementIr::NamedTheorem(
            LitexToLeanNamedTheoremIr {
                name: verification.name.clone(),
                theorem,
                expected_proof_step_count: verification.proof_step_count,
                proof_steps,
                stored_projections,
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &success.well_definedness,
                    &theorem_context,
                )?,
            },
        ))
    }

    fn build_litex_to_lean_ir_wrapped_contradiction(
        &self,
        result: &StmtResult,
        impossible_fact: &AtomicFact,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanContradictionIr, RuntimeError> {
        let Some(success) = result.non_factual_success() else {
            return Err(litex_to_lean_ir_error(
                &result.line_file(),
                "impossible branch did not retain a proof-scope result",
            ));
        };
        build_litex_to_lean_ir_contradiction_results(
            self,
            &success.inside_results,
            impossible_fact,
            context,
        )
    }

    fn build_litex_to_lean_ir_fact_from_success(
        &self,
        success: &FactualStmtSuccess,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        self.build_litex_to_lean_ir_fact_from_success_with_context(
            success,
            &LitexToLeanIrConstructionContext::default(),
        )
    }

    fn build_litex_to_lean_ir_projected_forall_statement(
        &self,
        success: &FactualStmtSuccess,
        source: LitexToLeanFactIr,
        mut excluded: HashSet<String>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let facts = self.build_litex_to_lean_ir_forall_projections(
            &success.infers,
            &source,
            &mut excluded,
        )?;
        let Fact::ForallFact(source_forall) = &source.proposition else {
            return Err(litex_to_lean_ir_error(
                &source.proposition.line_file(),
                "a verified non-forall fact was not assigned a stored FactId",
            ));
        };
        if facts.is_empty() {
            return Err(litex_to_lean_ir_error(
                &source_forall.line_file,
                "a verified forall had neither a FactId nor stored projections",
            ));
        }

        Ok(LitexToLeanStatementIr::ProjectedForall(
            LitexToLeanProjectedForallIr {
                source: source.proposition,
                facts,
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &success.well_definedness,
                    &self.well_definedness_context_for_factual_success(success),
                )?,
            },
        ))
    }

    fn build_litex_to_lean_ir_forall_projections(
        &self,
        infer_result: &InferResult,
        source: &LitexToLeanFactIr,
        excluded: &mut HashSet<String>,
    ) -> Result<Vec<LitexToLeanFactIr>, RuntimeError> {
        let Fact::ForallFact(source_forall) = &source.proposition else {
            return Err(litex_to_lean_ir_error(
                &source.proposition.line_file(),
                "a verified non-forall fact was not assigned a stored FactId",
            ));
        };
        let LitexToLeanFactProofIr::ForallIntroduction {
            parameter_premises,
            premises,
            inferred_premises,
            conclusions,
        } = &source.proof
        else {
            return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
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
        for output in infer_result.store_fact_outputs.iter() {
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
                    litex_to_lean_ir_error(
                        &proposition.line_file(),
                        "a stored forall projection reached Litex-to-Lean without a FactId",
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
                        return Err(litex_to_lean_ir_error(
                            &projected.line_file,
                            "a stored forall projection introduced a new binder",
                        ));
                    };
                    if last_source_index.is_some_and(|last| source_index <= last)
                        || !param_types_match_for_projection(source_type, projected_type)
                    {
                        return Err(litex_to_lean_ir_error(
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
                        return Err(litex_to_lean_ir_error(
                            &projected.line_file,
                            "a stored forall projection introduced a new conclusion",
                        ));
                    };
                    used_source_conclusions.insert(source_index);
                    projected_conclusions.push(conclusions[source_index].clone());
                }
                if projected_conclusions.is_empty() {
                    return Err(litex_to_lean_ir_error(
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
                facts.push(LitexToLeanFactIr {
                    fact_id: Some(fact_id),
                    proposition: proposition.clone(),
                    proof: LitexToLeanFactProofIr::ForallIntroduction {
                        parameter_premises: projected_parameter_premises,
                        premises: premises.clone(),
                        inferred_premises: projected_inferred_premises,
                        conclusions: projected_conclusions,
                    },
                });
            }
        }
        Ok(facts)
    }

    fn well_definedness_context_for_factual_success(
        &self,
        success: &FactualStmtSuccess,
    ) -> LitexToLeanIrConstructionContext {
        match success.underlying_verified_by() {
            VerifiedByResult::ForallProof(result) => LitexToLeanIrConstructionContext::default()
                .with_infer_result(&result.assumption_infers),
            _ => LitexToLeanIrConstructionContext::default(),
        }
    }

    fn build_litex_to_lean_ir_well_definedness_certificate(
        &self,
        certificate: &WellDefinednessCertificate,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanWellDefinednessCertificateIr, RuntimeError> {
        let mut facts = Vec::with_capacity(certificate.facts.len());
        for evidence in certificate.facts.iter() {
            let fact = self.build_litex_to_lean_ir_fact_from_success_with_context(
                evidence.proof.as_ref(),
                context,
            )?;
            if fact.proposition.to_string() != evidence.proof.stmt.to_string() {
                return Err(litex_to_lean_ir_error(
                    &evidence.proof.stmt.line_file(),
                    "well-definedness certificate proof changed its proposition during IR lowering",
                ));
            }
            facts.push(LitexToLeanWellDefinednessFactIr {
                certificate_id: evidence.certificate_id,
                well_defined_fact_id: evidence.well_defined_fact_id,
                role: evidence.role,
                expected_proposition: evidence.proof.stmt.clone(),
                fact,
            });
        }
        let facts_by_id = facts
            .iter()
            .map(|evidence| (evidence.certificate_id, &evidence.expected_proposition))
            .collect::<HashMap<_, _>>();
        let facts_by_well_defined_id = facts
            .iter()
            .map(|evidence| {
                (
                    evidence.well_defined_fact_id,
                    &evidence.expected_proposition,
                )
            })
            .collect::<HashMap<_, _>>();
        let mut objects = Vec::with_capacity(certificate.objects.len());
        let mut objects_by_id = HashMap::new();
        for evidence in certificate.objects.iter() {
            if evidence
                .fact_ids
                .iter()
                .any(|certificate_id| !facts_by_id.contains_key(certificate_id))
            {
                return Err(litex_to_lean_ir_error(
                    &default_line_file(),
                    "well-definedness object proof references a missing fact certificate",
                ));
            }
            if objects_by_id
                .insert(evidence.well_defined_obj_proof_id, evidence.object.clone())
                .is_some()
            {
                return Err(litex_to_lean_ir_error(
                    &default_line_file(),
                    "well-definedness object proof ID is duplicated",
                ));
            }
            let intrinsic_result_set = evidence
                .intrinsic_result_set
                .as_ref()
                .map(|set| {
                    LitexToLeanObjectIr::lower(set)
                        .map_err(|message| litex_to_lean_ir_error(&default_line_file(), message))
                })
                .transpose()?;
            let target_requirements = evidence
                .target_requirements
                .iter()
                .map(|requirement| {
                    let Some(expected) = facts_by_well_defined_id.get(&requirement.fact_id) else {
                        return Err(litex_to_lean_ir_error(
                            &requirement.expected_proposition.line_file(),
                            "well-defined object target requirement references a missing fact",
                        ));
                    };
                    if expected.to_string() != requirement.expected_proposition.to_string() {
                        return Err(litex_to_lean_ir_error(
                            &requirement.expected_proposition.line_file(),
                            "well-defined object target requirement changed its proposition",
                        ));
                    }
                    Ok(LitexToLeanWellDefinednessObjectRequirementIr {
                        role: requirement.role,
                        well_defined_fact_id: requirement.fact_id,
                        expected_proposition: requirement.expected_proposition.clone(),
                    })
                })
                .collect::<Result<Vec<_>, RuntimeError>>()?;
            objects.push(LitexToLeanWellDefinednessObjectIr {
                well_defined_obj_proof_id: evidence.well_defined_obj_proof_id,
                source_object: evidence.object.clone(),
                intrinsic_result_set,
                child_proof_ids: evidence.child_proof_ids.clone(),
                well_defined_fact_ids: evidence.well_defined_fact_ids.clone(),
                target_requirements,
                fact_ids: evidence.fact_ids.clone(),
            });
        }
        for root_use in certificate.root_proof_uses.iter() {
            if !objects_by_id.contains_key(&root_use.well_defined_obj_proof_id) {
                return Err(litex_to_lean_ir_error(
                    &default_line_file(),
                    "well-definedness root use references a missing object proof",
                ));
            }
        }
        let mut target_requirements = Vec::with_capacity(certificate.target_requirements.len());
        for requirement in certificate.target_requirements.iter() {
            if requirement.role == WellDefinednessRequirementRole::SourceObjectRequirement {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement has an audit-only role",
                ));
            }
            let Some(expected_fact) = facts_by_id.get(&requirement.certificate_id) else {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement references a missing fact certificate",
                ));
            };
            if expected_fact.to_string() != requirement.expected_proposition.to_string() {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement changed its verifier proposition",
                ));
            }
            let Some(source_object) = objects_by_id.get(&requirement.well_defined_obj_proof_id)
            else {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement references a missing object proof",
                ));
            };
            let Obj::FnObj(_) = source_object else {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement is not owned by a function application",
                ));
            };
            target_requirements.push(LitexToLeanWellDefinednessTargetRequirementIr {
                source_occurrence_id: requirement.source_occurrence_id,
                well_defined_obj_proof_id: requirement.well_defined_obj_proof_id,
                phase: requirement.phase,
                role: requirement.role,
                certificate_id: requirement.certificate_id,
                well_defined_fact_id: requirement.well_defined_fact_id,
                expected_proposition: requirement.expected_proposition.clone(),
            });
        }
        Ok(LitexToLeanWellDefinednessCertificateIr {
            root_proof_ids: certificate.root_proof_ids.clone(),
            root_proof_uses: certificate.root_proof_uses.clone(),
            facts,
            objects,
            target_requirements,
            parameter_facts: certificate
                .parameter_facts
                .iter()
                .map(|evidence| LitexToLeanWellDefinednessParameterFactIr {
                    symbol_id: evidence.symbol_id,
                    fact_id: evidence.fact_id,
                    proposition: evidence.proposition.clone(),
                })
                .collect(),
        })
    }

    fn build_litex_to_lean_ir_fact_from_success_with_context(
        &self,
        success: &FactualStmtSuccess,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        Ok(LitexToLeanFactIr {
            fact_id: success.fact_id,
            proposition: success.stmt.clone(),
            proof: self.build_litex_to_lean_ir_verified_by(
                &success.stmt,
                success.fact_id,
                &success.verified_by,
                context,
            )?,
        })
    }

    fn build_litex_to_lean_ir_fact_from_result(
        &self,
        result: &StmtResult,
        result_context: &str,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        let Some(success) = result.factual_success() else {
            return Ok(LitexToLeanFactIr {
                fact_id: None,
                proposition: result
                    .as_fact_unknown()
                    .map(|unknown| unknown.goal().clone())
                    .unwrap_or_else(|| {
                        NormalAtomicFact::new(
                            AtomicName::WithoutMod("compile_to_lean_unknown_subgoal".to_string()),
                            vec![],
                            result.line_file(),
                        )
                        .into()
                    }),
                proof: LitexToLeanFactProofIr::Unsupported {
                    reason: format!("{} did not return a factual success", result_context),
                },
            });
        };
        self.build_litex_to_lean_ir_fact_from_success_with_context(success, context)
    }

    fn build_litex_to_lean_ir_checked_definition_replay(
        &self,
        goal: &Fact,
        replay: &CheckedDefinitionReplayEvidence,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(goal_equality)) = goal else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition replay was attached to a non-equality goal",
            ));
        };
        let (expected_application, expected_other) = if replay.application_is_left {
            (&goal_equality.left, &goal_equality.right)
        } else {
            (&goal_equality.right, &goal_equality.left)
        };
        if obj_equality_key(expected_application) != obj_equality_key(&replay.application_side)
            || obj_equality_key(expected_other) != obj_equality_key(&replay.other_side)
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition replay does not match the recorded goal orientation",
            ));
        }
        if !replay.reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(&replay.reduced, &replay.other_side)
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "the current Litex-to-Lean function-definition replay adapter requires an alpha-equivalent unfolded result",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) = &replay.defining_equality
        else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition replay source is not a defining equality",
            ));
        };
        if obj_equality_key(&defining_equality.left) != obj_equality_key(&replay.definition_object)
            || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition replay source does not define the recorded function object",
            ));
        }
        let definition = LitexToLeanObjectIr::lower(&replay.definition_object)
            .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
        if !matches!(definition, LitexToLeanObjectIr::Symbol { .. }) {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition replay currently requires a named function symbol",
            ));
        }
        for object in [
            &replay.application_side,
            &replay.reduced,
            &replay.other_side,
        ] {
            LitexToLeanObjectIr::lower(object)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
        }
        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::CheckedFunctionDefinitionReplay {
                definition,
                defining_equality_fact_id: replay.defining_equality_fact_id,
                defining_equality: replay.defining_equality.clone(),
                expected_target: goal.clone(),
                application_side: replay.application_side.clone(),
                reduced: replay.reduced.clone(),
                other_side: replay.other_side.clone(),
                application_is_left: replay.application_is_left,
                reduced_matches_other_by_alpha: replay.reduced_matches_other_by_alpha,
            },
            parameter_requirements: Vec::new(),
            premises: Vec::new(),
        })
    }

    fn build_litex_to_lean_ir_definition_reduction(
        &self,
        goal: &Fact,
        definition: &DefPropStmt,
        parameter_checks: &[StmtResult],
        clause_facts: &[Fact],
        clause_checks: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let (expected_parameter_requirements, expected_clauses) =
            self.instantiated_prop_definition_components(definition, goal)?;
        if parameter_checks.len() != expected_parameter_requirements.len()
            || clause_facts.len() != expected_clauses.len()
            || clause_checks.len() != expected_clauses.len()
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "concrete prop reduction retained the wrong number of parameter or clause checks",
            ));
        }

        let mut parameter_requirements = Vec::with_capacity(parameter_checks.len());
        for (result, expected) in parameter_checks
            .iter()
            .zip(expected_parameter_requirements.iter())
        {
            let mut requirement = self.build_litex_to_lean_ir_fact_from_result(
                result,
                "concrete prop parameter requirement",
                context,
            )?;
            if requirement.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "concrete prop parameter check `{}` does not match expected `{}`",
                        requirement.proposition, expected
                    ),
                ));
            }
            requirement.fact_id = None;
            parameter_requirements.push(requirement);
        }

        let mut premises = Vec::with_capacity(clause_checks.len());
        for ((retained, result), expected) in clause_facts
            .iter()
            .zip(clause_checks.iter())
            .zip(expected_clauses.iter())
        {
            if retained.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "concrete prop retained clause `{}` does not match expected `{}`",
                        retained, expected
                    ),
                ));
            }
            let mut premise = self.build_litex_to_lean_ir_fact_from_result(
                result,
                "concrete prop definition clause",
                context,
            )?;
            if premise.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "concrete prop clause proof `{}` does not match expected `{}`",
                        premise.proposition, expected
                    ),
                ));
            }
            premise.fact_id = None;
            premises.push(premise);
        }

        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::DefinitionReduction {
                definition: definition.name.clone(),
                expected_parameter_requirements,
                expected_clauses,
            },
            parameter_requirements,
            premises,
        })
    }

    fn instantiated_prop_definition_components(
        &self,
        definition: &DefPropStmt,
        target: &Fact,
    ) -> Result<(Vec<Fact>, Vec<Fact>), RuntimeError> {
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target)) = target else {
            return Err(litex_to_lean_ir_error(
                &target.line_file(),
                "concrete prop reduction targets a non-predicate fact",
            ));
        };
        if target.predicate.to_string() != definition.name
            || target.body.len() != definition.params_def_with_type.number_of_params()
        {
            return Err(litex_to_lean_ir_error(
                &target.line_file,
                "concrete prop reduction target does not match its retained definition",
            ));
        }
        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            &definition.params_def_with_type,
            &target.body,
            ParamObjType::DefHeader,
        )?;
        let flat_types = definition
            .params_def_with_type
            .flat_instantiated_types_for_args(&instantiated_types);
        let parameter_requirements = target
            .body
            .iter()
            .zip(flat_types.iter())
            .map(|(argument, param_type)| {
                object_type_fact_for_litex_to_lean(
                    argument.clone(),
                    param_type,
                    target.line_file.clone(),
                )
            })
            .collect::<Vec<_>>();
        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(target.body.as_slice());
        let clauses = definition
            .iff_facts
            .iter()
            .map(|clause| {
                self.inst_fact(
                    clause,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(target.line_file.clone()),
                )
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        Ok((parameter_requirements, clauses))
    }

    fn build_litex_to_lean_ir_verified_by(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        verified_by: &VerifiedByResult,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) => self
                .build_litex_to_lean_ir_builtin_rule_application(
                    goal,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                ),
            VerifiedByResult::BuiltinStrategy(result) => self
                .build_litex_to_lean_ir_builtin_rule_application(
                    goal,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                ),
            VerifiedByResult::Fact(result) => {
                if let Some(replay) = result.checked_definition_replay.as_ref() {
                    return self.build_litex_to_lean_ir_checked_definition_replay(goal, replay);
                }
                if let Some(evidence) = result.definition_reduction.as_ref() {
                    let Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) =
                        result.cite_what.as_ref()
                    else {
                        return Err(litex_to_lean_ir_error(
                            &goal.line_file(),
                            "concrete prop reduction evidence cites a non-prop statement",
                        ));
                    };
                    return self.build_litex_to_lean_ir_definition_reduction(
                        goal,
                        definition,
                        &evidence.parameter_checks,
                        &evidence.clause_facts,
                        &evidence.clause_checks,
                        context,
                    );
                }
                match result.cite_what.as_ref() {
                    Stmt::Fact(source_fact) => self.build_litex_to_lean_ir_fact_citation(
                        goal,
                        goal_fact_id,
                        source_fact,
                        result.source_fact_id,
                        result.equality_transport.as_ref(),
                        result.fact_transformation.as_ref(),
                        context,
                    ),
                    Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => {
                        Ok(LitexToLeanFactProofIr::Unsupported {
                            reason:
                                "concrete prop citation has no retained parameter and clause checks"
                                    .to_string(),
                        })
                    }
                    Stmt::DefStrategyStmt(strategy) => Ok(LitexToLeanFactProofIr::UserStrategy {
                        name: strategy.name.clone(),
                    }),
                    cited => Ok(LitexToLeanFactProofIr::Unsupported {
                        reason: format!(
                            "citation kind `{}` is not represented by the Litex-to-Lean MVP",
                            cited.stmt_type_name()
                        ),
                    }),
                }
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.build_litex_to_lean_ir_known_forall(goal, result, context)
            }
            VerifiedByResult::VerifiedBys(result) => {
                let mut steps = Vec::with_capacity(result.cite_what.len());
                for step in result.cite_what.iter() {
                    steps.push(self.build_litex_to_lean_ir_verified_bys_step(
                        step,
                        goal,
                        goal_fact_id,
                        context,
                    )?);
                }
                Ok(LitexToLeanFactProofIr::Composite { steps })
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
                            litex_to_lean_ir_error(
                                &fact.line_file(),
                                "a forall parameter premise reached Litex-to-Lean without a FactId",
                            )
                        })?;
                        Ok(LitexToLeanLocalPremiseIr::new(fact_id, fact))
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
                            litex_to_lean_ir_error(
                                &fact.line_file(),
                                "a forall domain premise reached Litex-to-Lean without a FactId",
                            )
                        })?;
                    premises.push(LitexToLeanLocalPremiseIr::new(fact_id, fact));
                }
                let inferred_premises = self.build_litex_to_lean_ir_supported_inferred_premises(
                    &result.assumption_infers,
                )?;
                let conclusion_context = context.with_infer_result(&result.assumption_infers);
                let mut conclusions = Vec::with_capacity(result.proves.len());
                for proved in result.proves.iter() {
                    conclusions.push(self.build_litex_to_lean_ir_fact_from_result(
                        proved.result.as_ref(),
                        "forall conclusion",
                        &conclusion_context,
                    )?);
                }
                Ok(LitexToLeanFactProofIr::ForallIntroduction {
                    parameter_premises,
                    premises,
                    inferred_premises,
                    conclusions,
                })
            }
            VerifiedByResult::StatementMemo(source) => Ok(LitexToLeanFactProofIr::Memo {
                proof: Box::new(self.build_litex_to_lean_ir_verified_by(
                    goal,
                    source.fact_id.or(goal_fact_id),
                    &source.verified_by,
                    context,
                )?),
            }),
        }
    }

    fn build_litex_to_lean_ir_fact_citation(
        &self,
        goal: &Fact,
        goal_fact_id: Option<FactId>,
        source_fact: &Fact,
        recorded_source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
        fact_transformation: Option<&FactTransformationEvidence>,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let source_fact_id = match recorded_source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, goal, goal_fact_id, context)?,
        };
        if source_fact_id.is_none()
            && equality_transport.is_none()
            && fact_transformation.is_none()
            && crate::litex_to_lean_ir::facts_are_comparison_notation_duals(source_fact, goal)
        {
            // Binder-owning source objects (for example an anonymous function
            // used while checking `$prime`) can prove this relation in a
            // temporary assumption scope that has no stored FactId. Preserve
            // the exact source/target pair; only the generalized WD-helper
            // emitter may discharge the missing premise explicitly.
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ComparisonNotationDuality {
                    expected_source: source_fact.clone(),
                    expected_target: goal.clone(),
                },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        let Some(source_fact_id) = source_fact_id else {
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: format!("verified citation `{}` has no stored FactId", source_fact),
            });
        };

        // Preserve the existing closed-membership certificate even when the
        // verifier also records how a differently spelled citation resolved
        // to this closed goal. The checked target rule is dependency-free and
        // more precise than replaying an incidental citation route.
        if source_fact.to_string() != goal.to_string()
            && (crate::litex_to_lean_ir::is_closed_real_membership(goal)
                || crate::litex_to_lean_ir::closed_compact_numeric_set_fact(goal).is_some())
        {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: if crate::litex_to_lean_ir::is_closed_real_membership(goal) {
                    LitexToLeanProofRuleIr::ClosedRealMembership
                } else {
                    LitexToLeanProofRuleIr::ClosedNumericReflection {
                        target_set: crate::litex_to_lean_ir::closed_compact_numeric_set_fact(goal)
                            .unwrap(),
                    }
                },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }

        if equality_transport.is_none() && fact_transformation.is_none() {
            if source_fact.to_string() == goal.to_string() {
                return Ok(LitexToLeanFactProofIr::KnownFactCitation { source_fact_id });
            }
            if crate::litex_to_lean_ir::facts_are_comparison_notation_duals(source_fact, goal) {
                return Ok(LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ComparisonNotationDuality {
                        expected_source: source_fact.clone(),
                        expected_target: goal.clone(),
                    },
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        fact_id: Some(source_fact_id),
                        proposition: source_fact.clone(),
                        proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                    }],
                });
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
                    return Ok(LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                        source_fact_id,
                        source_proposition: source_fact.clone(),
                    });
                }
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::OtherUnsupported {
                    name: format!(
                        "citation `{}` changed goal `{}` without structured rewrite evidence",
                        source_fact, goal
                    ),
                },
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    fact_id: Some(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                }],
            });
        }

        let mut current = LitexToLeanFactIr {
            fact_id: Some(source_fact_id),
            proposition: source_fact.clone(),
            proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
        };
        let citation_target = fact_transformation
            .map(|transformation| &transformation.source)
            .unwrap_or(goal);
        if let Some(equality_transport) = equality_transport {
            current = self.build_litex_to_lean_ir_equality_rewrite_fact(
                citation_target,
                current,
                equality_transport,
            );
        } else if current.proposition.to_string() != citation_target.to_string() {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::OtherUnsupported {
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
                            return Ok(LitexToLeanFactProofIr::RuleApplication {
                                rule: LitexToLeanProofRuleIr::OtherUnsupported {
                                    name: format!(
                                        "normalization source `{}` does not align with result `{}`",
                                        current.proposition, step.result
                                    ),
                                },
                                parameter_requirements: Vec::new(),
                                premises: vec![current],
                            });
                        }
                        LitexToLeanFactIr {
                            fact_id: None,
                            proposition: step.result.clone(),
                            proof: LitexToLeanFactProofIr::RuleApplication {
                                rule: LitexToLeanProofRuleIr::Normalization {
                                    kind:
                                        LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                                },
                                parameter_requirements: Vec::new(),
                                premises: vec![current],
                            },
                        }
                    }
                    FactTransformationRule::EqualityRewrite(evidence) => self
                        .build_litex_to_lean_ir_equality_rewrite_fact(
                            &step.result,
                            current,
                            evidence,
                        ),
                };
            }
        }

        if current.proposition.to_string() != goal.to_string() {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::OtherUnsupported {
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

    fn build_litex_to_lean_ir_equality_rewrite_fact(
        &self,
        result: &Fact,
        source: LitexToLeanFactIr,
        equality_transport: &EqualityTransportEvidence,
    ) -> LitexToLeanFactIr {
        if equality_transport.steps.is_empty() {
            if source.proposition.to_string() == result.to_string() {
                return source;
            }
            return LitexToLeanFactIr {
                fact_id: None,
                proposition: result.clone(),
                proof: LitexToLeanFactProofIr::Unsupported {
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
                return LitexToLeanFactIr {
                    fact_id: None,
                    proposition: result.clone(),
                    proof: LitexToLeanFactProofIr::Unsupported {
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
                LitexToLeanEqualityRewriteDirectionIr::Forward
            } else if from_key == right_key && to_key == left_key {
                LitexToLeanEqualityRewriteDirectionIr::Backward
            } else {
                return LitexToLeanFactIr {
                    fact_id: None,
                    proposition: result.clone(),
                    proof: LitexToLeanFactProofIr::Unsupported {
                        reason: format!(
                            "equality rewrite edge `{}` -> `{}` is not oriented by `{}`",
                            rewrite.from, rewrite.to, equality_fact
                        ),
                    },
                };
            };
            premises.push(LitexToLeanFactIr {
                fact_id: Some(equality_fact_id),
                proposition: equality_fact,
                proof: LitexToLeanFactProofIr::KnownFactCitation {
                    source_fact_id: equality_fact_id,
                },
            });
            steps.push(LitexToLeanEqualityRewriteStepIr {
                from: rewrite.from.clone(),
                to: rewrite.to.clone(),
                direction,
            });
        }

        LitexToLeanFactIr {
            fact_id: None,
            proposition: result.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::EqualityRewrite(LitexToLeanEqualityRewriteIr {
                    steps,
                }),
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
        context: &LitexToLeanIrConstructionContext,
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

    fn build_litex_to_lean_ir_known_forall(
        &self,
        goal: &Fact,
        result: &KnownForallInstantiationResult,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let Stmt::Fact(source_fact) = result.cite_what.as_ref() else {
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: "known-forall verification did not cite a fact".to_string(),
            });
        };
        let Fact::ForallFact(source_forall) = source_fact else {
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: "known-forall verification cited a non-forall fact".to_string(),
            });
        };
        let source_fact_id = match result.source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, source_fact, None, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: format!("known forall `{}` has no stored FactId", source_fact),
            });
        };

        let mut param_types = Vec::new();
        for group in source_forall.params_def_with_type.groups.iter() {
            if group.params.is_empty() {
                return Ok(LitexToLeanFactProofIr::Unsupported {
                    reason: "known forall contains an empty parameter group".to_string(),
                });
            }
            let param_type = build_litex_to_lean_ir_parameter_type(&group.param_type)?;
            for _ in group.params.iter() {
                param_types.push(param_type.clone());
            }
        }
        if result.instantiation.len() != param_types.len() {
            return Ok(LitexToLeanFactProofIr::Unsupported {
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
            .map(|(item, param_type)| LitexToLeanKnownForallArgumentIr {
                param: item.param.clone(),
                argument: item.arg_obj.clone(),
                param_type,
            })
            .collect::<Vec<_>>();
        let mut parameter_requirements = Vec::new();
        let mut requirements = Vec::new();
        for requirement in result.requirements.iter() {
            let requirement_ir = self.build_litex_to_lean_ir_fact_from_result(
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
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: format!(
                    "known forall `{}` recorded {} arguments but {} parameter requirements",
                    source_fact,
                    arguments.len(),
                    parameter_requirements.len()
                ),
            });
        }

        let Some(source_conclusion) = source_forall.then_facts.first() else {
            return Ok(LitexToLeanFactProofIr::Unsupported {
                reason: format!("known forall `{}` has no conclusion", source_fact),
            });
        };
        if source_forall.then_facts.len() != 1 {
            return Ok(LitexToLeanFactProofIr::Unsupported {
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
        let application = LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::KnownForallInstantiation {
                source_fact_id,
                arguments,
            },
            parameter_requirements,
            premises: requirements,
        };
        if instantiated_conclusion.to_string() == goal.to_string() {
            return Ok(application);
        }

        let instantiated_fact = LitexToLeanFactIr {
            fact_id: None,
            proposition: instantiated_conclusion.clone(),
            proof: application,
        };
        if facts_align_by_rational_normalization(&instantiated_conclusion, goal) {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                },
                parameter_requirements: Vec::new(),
                premises: vec![instantiated_fact],
            });
        }

        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::OtherUnsupported {
                name: format!(
                    "known-forall instance `{}` does not structurally match goal `{}`",
                    instantiated_conclusion, goal
                ),
            },
            parameter_requirements: Vec::new(),
            premises: vec![instantiated_fact],
        })
    }

    fn build_litex_to_lean_ir_builtin_rule_application(
        &self,
        goal: &Fact,
        label: &str,
        evidence: Option<&BuiltinRuleEvidence>,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        if let Some(BuiltinRuleEvidence::KnownEqualityPath(evidence)) = evidence {
            return self
                .build_litex_to_lean_ir_known_equality_path(goal, evidence, subgoals, context);
        }
        if let Some(BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence was retargeted",
                ));
            }
            let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
            if premises.len() != 1
                || premises[0].proposition.to_string()
                    != evidence.expected_head_membership.to_string()
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence lost its exact head-membership premise",
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(expected_target)) = &evidence.expected_target
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence retained a non-membership target",
                ));
            };
            let Obj::FnObj(expected_application) = &expected_target.element else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence retained a non-application target element",
                ));
            };
            let Fact::AtomicFact(AtomicFact::InFact(expected_head_membership)) =
                &evidence.expected_head_membership
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence retained a non-membership premise",
                ));
            };
            if !matches!(&expected_head_membership.set, Obj::FnSet(_)) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence retained a non-function-space head premise",
                ));
            }
            let expected_head: Obj = expected_application.head.as_ref().clone().into();
            if obj_equality_key(&expected_head_membership.element)
                != obj_equality_key(&expected_head)
                || !objs_equal_with_nested_binder_alpha_equivalence(
                    &expected_target.set,
                    &evidence.typed_return_set,
                )
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence changed its application head or typed return set",
                ));
            }
            let source_application = LitexToLeanObjectIr::lower(&expected_target.element)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let function_set = LitexToLeanObjectIr::lower(&expected_head_membership.set)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let typed_return_set = LitexToLeanObjectIr::lower(&evidence.typed_return_set)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            if !matches!(
                source_application,
                LitexToLeanObjectIr::FunctionApplication(_)
            ) || !matches!(function_set, LitexToLeanObjectIr::FunctionSet { .. })
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-application return membership evidence lowered to the wrong object constructors",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::FunctionApplicationReturnMembership {
                    source_application,
                    function_set,
                    typed_return_set,
                    expected_target: evidence.expected_target.clone(),
                    expected_head_membership: evidence.expected_head_membership.clone(),
                },
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string()
                || !subgoals.is_empty()
                || !crate::litex_to_lean_ir::is_closed_numeric_relation(goal)
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "closed numeric comparison evidence changed its checked target or gained premises",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedNumericComparison {
                    expected_target: evidence.expected_target.clone(),
                },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        if let Some(BuiltinRuleEvidence::RefinedNumericMembership(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "refined numeric membership evidence was retargeted after verification",
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(expected_target)) = &evidence.expected_target
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "refined numeric membership evidence retained a non-membership target",
                ));
            };
            let Obj::StandardSet(target_set) = &expected_target.set else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "refined numeric membership evidence retained a non-numeric target set",
                ));
            };
            let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
            if premises.len() != evidence.expected_premises.len()
                || premises.iter().zip(evidence.expected_premises.iter()).any(
                    |(actual, expected)| actual.proposition.to_string() != expected.to_string(),
                )
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "refined numeric membership evidence lost its exact constructor premises",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::RefinedNumericMembership {
                    target_set: *target_set,
                    expected_target: evidence.expected_target.clone(),
                    expected_premises: evidence.expected_premises.clone(),
                },
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::FunctionSetMembership(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence was retargeted after verification",
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(target)) = &evidence.expected_target else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence was attached to a non-membership fact",
                ));
            };
            if !matches!(&target.set, Obj::FnSet(_)) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence retained a non-function-space target",
                ));
            }
            let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
            if premises.len() != 1
                || premises[0].proposition.to_string() != evidence.expected_pointwise.to_string()
                || !matches!(&evidence.expected_pointwise, Fact::ForallFact(_))
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence did not retain its exact pointwise forall proof",
                ));
            }
            let element = LitexToLeanObjectIr::lower(&target.element)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let function_set = LitexToLeanObjectIr::lower(&target.set)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            if !matches!(function_set, LitexToLeanObjectIr::FunctionSet { .. }) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence lowered to a non-function-space object",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::FunctionSetMembership {
                    element,
                    function_set,
                    expected_target: evidence.expected_target.clone(),
                    expected_pointwise: evidence.expected_pointwise.clone(),
                },
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "set-builder membership evidence was retargeted after verification",
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(expected_target)) = &evidence.expected_target
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "set-builder membership evidence retained a non-membership target",
                ));
            };
            if !matches!(&expected_target.set, Obj::SetBuilder(_)) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "set-builder membership evidence retained a non-builder target set",
                ));
            }
            let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
            if premises.len() != evidence.expected_premises.len()
                || premises.iter().zip(evidence.expected_premises.iter()).any(
                    |(actual, expected)| actual.proposition.to_string() != expected.to_string(),
                )
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "set-builder membership evidence does not retain the exact ordered constructor premises",
                ));
            }
            let set_builder = LitexToLeanObjectIr::lower(&expected_target.set)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            if !matches!(set_builder, LitexToLeanObjectIr::SetBuilder(_)) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "set-builder membership evidence lowered to a non-builder object",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::SetBuilderMembership {
                    set_builder,
                    expected_target: evidence.expected_target.clone(),
                    expected_premises: evidence.expected_premises.clone(),
                },
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) = evidence {
            return self.build_litex_to_lean_ir_definition_projection_builtin_application(
                goal, evidence, subgoals, context,
            );
        }
        if let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) = evidence {
            return self.build_litex_to_lean_ir_registered_local_builtin_application(
                goal, evidence, subgoals, context,
            );
        }
        let rule = match evidence {
            Some(evidence) => LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::from_legacy_evidence(evidence).ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &goal.line_file(),
                        "registered local builtin reached legacy evidence lowering",
                    )
                })?,
            ),
            None => LitexToLeanProofRuleIr::from_verified_builtin_label(label, goal),
        };
        let premises = if matches!(
            rule,
            LitexToLeanProofRuleIr::Normalization {
                kind: LitexToLeanNormalizationKindIr::IntegerExpressionSimplification,
            }
        ) && crate::litex_to_lean_ir::is_checked_closed_integer_remainder_equality(
            goal,
        ) {
            // Closed integer reflection rechecks the complete target value in
            // the IR contract. Incidental verifier detours (currently through
            // injectivity of `exp`) are not semantic premises of that
            // certificate and must not leak into Lean replay.
            Vec::new()
        } else {
            self.build_litex_to_lean_ir_subgoals(subgoals, context)?
        };
        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule,
            parameter_requirements: Vec::new(),
            premises,
        })
    }

    fn build_litex_to_lean_ir_known_equality_path(
        &self,
        goal: &Fact,
        evidence: &KnownEqualityBuiltinRuleEvidence,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        if evidence.expected_target.to_string() != goal.to_string() || !subgoals.is_empty() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-equality evidence changed its target or gained verifier subgoals",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(target)) = &evidence.expected_target else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-equality evidence retained a non-equality target",
            ));
        };
        if evidence.steps.is_empty() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-equality evidence retained an empty non-reflexive path",
            ));
        }

        let mut current_key = obj_equality_key(&target.left);
        let target_key = obj_equality_key(&target.right);
        let mut premises = Vec::with_capacity(evidence.steps.len());
        let mut steps = Vec::with_capacity(evidence.steps.len());
        for step in evidence.steps.iter() {
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            if current_key != from_key {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "known-equality evidence contains a disconnected path",
                ));
            }

            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let direction = if from_key == left_key && to_key == right_key {
                LitexToLeanEqualityRewriteDirectionIr::Forward
            } else if from_key == right_key && to_key == left_key {
                LitexToLeanEqualityRewriteDirectionIr::Backward
            } else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "known-equality evidence contains an edge with invalid orientation",
                ));
            };

            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let available_fact_id = context
                .local_fact_ids
                .get(&equality_fact.to_string())
                .copied()
                .or(self.known_fact_id_for_fact(&equality_fact)?);
            if available_fact_id != Some(step.source_fact_id) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "known-equality edge `{equality_fact}` cites unavailable or mismatched FactId {}",
                        step.source_fact_id.value()
                    ),
                ));
            }
            premises.push(LitexToLeanFactIr {
                fact_id: Some(step.source_fact_id),
                proposition: equality_fact,
                proof: LitexToLeanFactProofIr::KnownFactCitation {
                    source_fact_id: step.source_fact_id,
                },
            });
            steps.push(LitexToLeanKnownEqualityStepIr {
                from: step.from.clone(),
                to: step.to.clone(),
                source_fact_id: step.source_fact_id,
                direction,
            });
            current_key = to_key;
        }
        if current_key != target_key {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-equality evidence does not end at the target right-hand side",
            ));
        }

        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::KnownEqualityPath(LitexToLeanKnownEqualityPathIr {
                steps,
            }),
            parameter_requirements: Vec::new(),
            premises,
        })
    }

    fn build_litex_to_lean_ir_definition_projection_builtin_application(
        &self,
        goal: &Fact,
        evidence: &DefinitionProjectionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let Fact::ExistFact(goal_existential) = goal else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "definition-projection evidence requires an existential target",
            ));
        };
        if !goal_existential.is_plain_exist() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "definition-projection evidence currently requires a positive `exist` target",
            ));
        }
        if subgoals.len() != 1 {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "definition-projection evidence must retain exactly one source proof",
            ));
        }

        let reconstructed = self.instantiate_existential_prop_definition(
            &evidence.fact,
            &evidence.definition,
            &goal.line_file(),
        )?;
        if !reconstructed.is_plain_exist()
            || Runtime::exist_fact_normalized_body_string(self, &reconstructed)?
                != Runtime::exist_fact_normalized_body_string(self, goal_existential)?
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "definition `{}` does not unfold source `{}` to target `{}`",
                    evidence.definition.name, evidence.fact, goal
                ),
            ));
        }

        let expected_source: Fact = evidence.fact.clone().into();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&expected_source)?;
        ensure_fact_objects_supported_by_litex_to_lean_ir(goal)?;
        let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
        if premises[0].proposition.to_string() != expected_source.to_string() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "definition-projection source proof `{}` does not certify `{}`",
                    premises[0].proposition, expected_source
                ),
            ));
        }

        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::DefinitionProjection {
                definition: evidence.definition.name.clone(),
                expected_source,
                expected_target: goal.clone(),
            },
            parameter_requirements: Vec::new(),
            premises,
        })
    }

    fn build_litex_to_lean_ir_registered_local_builtin_application(
        &self,
        goal: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let rules = registered_local_builtin_rules()?;
        let rule = rules
            .iter()
            .find(|rule| rule.id() == &evidence.rule_id)
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &goal.line_file(),
                    format!(
                        "unknown local builtin RuleId `{}`",
                        evidence.rule_id.as_str()
                    ),
                )
            })?;
        if rule.semantic_fingerprint() != &evidence.semantic_fingerprint {
            return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate has the wrong binding or requirement arity",
            ));
        }
        let Fact::AtomicFact(goal_atomic) = goal else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate target must be atomic",
            ));
        };
        let matched = match_conclusion(rule.schema(), goal_atomic, MatchLimits::default())
            .map_err(|error| litex_to_lean_ir_error(&goal.line_file(), error.message))?
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &goal.line_file(),
                    "local builtin certificate target does not match its registered schema",
                )
            })?;
        for (expected, actual) in matched.bindings().iter().zip(&evidence.bindings) {
            if !canonical_objs_equal(expected, actual, MatchLimits::default())
                .map_err(|error| litex_to_lean_ir_error(&goal.line_file(), error.message))?
            {
                return Err(litex_to_lean_ir_error(
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
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate has the wrong child-proof arity",
            ));
        }
        let children = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
        for (template, child) in expected_templates.iter().zip(&children) {
            let expected = self.inst_atomic_fact(
                template,
                &param_to_arg_map,
                ParamObjType::Forall,
                Some(&goal.line_file()),
            )?;
            let Fact::AtomicFact(actual) = &child.proposition else {
                return Err(litex_to_lean_ir_error(
                    &child.proposition.line_file(),
                    "local builtin child proof is not atomic",
                ));
            };
            if !canonical_atomic_facts_equal(&expected, actual, MatchLimits::default()).map_err(
                |error| litex_to_lean_ir_error(&child.proposition.line_file(), error.message),
            )? {
                return Err(litex_to_lean_ir_error(
                    &child.proposition.line_file(),
                    "local builtin child proof does not match its instantiated schema fact",
                ));
            }
        }

        let mut bindings = Vec::with_capacity(evidence.bindings.len());
        for (variable, object) in rule.schema().variables.iter().zip(&evidence.bindings) {
            let object = LitexToLeanObjectIr::lower(object)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let instantiated_param_type = self.inst_param_type(
                &variable.param_type,
                &param_to_arg_map,
                ParamObjType::Forall,
            )?;
            bindings.push(LitexToLeanTypedBoundObjectIr {
                object,
                param_type: build_litex_to_lean_ir_parameter_type(&instantiated_param_type)?,
            });
        }
        let premises = children.split_at(evidence.parameter_requirement_count);
        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::RegisteredRule(LitexToLeanRegisteredRuleApplicationIr {
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

    fn build_litex_to_lean_ir_subgoals(
        &self,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<Vec<LitexToLeanFactIr>, RuntimeError> {
        subgoals
            .iter()
            .map(|result| {
                self.build_litex_to_lean_ir_fact_from_result(result, "builtin subgoal", context)
            })
            .collect()
    }

    fn build_litex_to_lean_ir_verified_bys_step(
        &self,
        step: &VerifiedBysEnum,
        enclosing_goal: &Fact,
        enclosing_goal_fact_id: Option<FactId>,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
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
            VerifiedBysEnum::ByBuiltinRule(result) => Ok(LitexToLeanFactIr {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.build_litex_to_lean_ir_builtin_rule_application(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByBuiltinStrategy(result) => Ok(LitexToLeanFactIr {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.build_litex_to_lean_ir_builtin_rule_application(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByFact(result) => {
                let proof = if let Some(evidence) = result.definition_reduction.as_ref() {
                    let Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(definition)) =
                        result.cite_what.as_ref()
                    else {
                        return Err(litex_to_lean_ir_error(
                            &result.verify_what.line_file(),
                            "composite concrete prop reduction cites a non-prop statement",
                        ));
                    };
                    self.build_litex_to_lean_ir_definition_reduction(
                        &result.verify_what,
                        definition,
                        &evidence.parameter_checks,
                        &evidence.clause_facts,
                        &evidence.clause_checks,
                        context,
                    )?
                } else {
                    match result.cite_what.as_ref() {
                    Stmt::Fact(source) => self.build_litex_to_lean_ir_fact_citation(
                        &result.verify_what,
                        step_fact_id(&result.verify_what)?,
                        source,
                        result.source_fact_id,
                        result.equality_transport.as_ref(),
                        result.fact_transformation.as_ref(),
                        context,
                    )?,
                    Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => {
                        LitexToLeanFactProofIr::Unsupported {
                            reason: "concrete prop citation has no retained parameter and clause checks"
                                .to_string(),
                        }
                    }
                    cited => LitexToLeanFactProofIr::Unsupported {
                        reason: format!("unsupported composite citation `{}`", cited),
                    },
                }
                };
                Ok(LitexToLeanFactIr {
                    fact_id: step_fact_id(&result.verify_what)?,
                    proposition: result.verify_what.clone(),
                    proof,
                })
            }
            VerifiedBysEnum::ByKnownForall(result) => Ok(LitexToLeanFactIr {
                fact_id: step_fact_id(&result.verify_what)?,
                proposition: result.verify_what.clone(),
                proof: self.build_litex_to_lean_ir_known_forall(
                    &result.verify_what,
                    &result.result,
                    context,
                )?,
            }),
            VerifiedBysEnum::ByStatementMemo(goal, source) => Ok(LitexToLeanFactIr {
                fact_id: step_fact_id(goal)?,
                proposition: goal.clone(),
                proof: LitexToLeanFactProofIr::Memo {
                    proof: Box::new(self.build_litex_to_lean_ir_verified_by(
                        goal,
                        source.fact_id.or(step_fact_id(goal)?),
                        &source.verified_by,
                        context,
                    )?),
                },
            }),
        }
    }

    fn build_litex_to_lean_ir_inferred_facts(
        &self,
        infer_result: &InferResult,
        excluded: &HashSet<String>,
    ) -> Result<Vec<LitexToLeanFactIr>, RuntimeError> {
        let mut seen = excluded.clone();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            let source_fact = &output.itself_and_why_itself_is_stored.0;
            let source_id = output.fact_id.or(self.known_fact_id_for_fact(source_fact)?);
            let source_key = source_fact.to_string();
            if seen.insert(source_key) {
                let proof = if let Some(target_set) =
                    crate::litex_to_lean_ir::closed_compact_numeric_set_fact(source_fact)
                {
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ClosedNumericReflection { target_set },
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
                    }
                } else {
                    LitexToLeanFactProofIr::Inference {
                        source_fact_id: None,
                        reason: output.itself_and_why_itself_is_stored.1.clone(),
                    }
                };
                // Internal inferences are emitted only when this backend has a
                // checked proof adapter. A later citation still fails closed
                // because no Lean declaration is registered for an omitted fact.
                if !matches!(proof, LitexToLeanFactProofIr::Inference { .. }) {
                    inferred.push(LitexToLeanFactIr {
                        fact_id: source_id,
                        proposition: source_fact.clone(),
                        proof,
                    });
                }
            }
            if output.inferred_fact_ids.len() != output.inferred_facts.len() {
                return Err(litex_to_lean_ir_error(
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
                let proof = build_litex_to_lean_ir_inferred_fact_proof(
                    self,
                    source_fact,
                    source_id,
                    fact,
                    &output.itself_and_why_itself_is_stored.1,
                )?;
                if matches!(proof, LitexToLeanFactProofIr::Inference { .. }) {
                    continue;
                }
                inferred.push(LitexToLeanFactIr {
                    fact_id: (*recorded_fact_id).or(self.known_fact_id_for_fact(fact)?),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }

    fn build_litex_to_lean_ir_supported_inferred_premises(
        &self,
        infer_result: &InferResult,
    ) -> Result<Vec<LitexToLeanFactIr>, RuntimeError> {
        let mut seen = HashSet::new();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            if output.inferred_fact_ids.len() != output.inferred_facts.len() {
                return Err(litex_to_lean_ir_error(
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
                let proof = build_litex_to_lean_ir_inferred_fact_proof(
                    self,
                    source_fact,
                    Some(source_fact_id),
                    fact,
                    &output.itself_and_why_itself_is_stored.1,
                )?;
                if matches!(proof, LitexToLeanFactProofIr::Inference { .. }) {
                    continue;
                }
                let fact_id = (*fact_id).ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &fact.line_file(),
                        "a supported forall inference reached Litex-to-Lean without a FactId",
                    )
                })?;
                inferred.push(LitexToLeanFactIr {
                    fact_id: Some(fact_id),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }
}

fn build_litex_to_lean_ir_inferred_fact_proof(
    runtime: &Runtime,
    source_fact: &Fact,
    source_fact_id: Option<FactId>,
    inferred_fact: &Fact,
    reason: &str,
) -> Result<LitexToLeanFactProofIr, RuntimeError> {
    if let (Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)), Some(source_fact_id)) =
        (source_fact, source_fact_id)
    {
        if let Some(definition) =
            runtime.get_active_prop_definition_by_name(&source.predicate.to_string())
        {
            let (parameter_requirements, clauses) =
                runtime.instantiated_prop_definition_components(&definition, source_fact)?;
            if parameter_requirements
                .iter()
                .chain(clauses.iter())
                .any(|component| component.to_string() == inferred_fact.to_string())
            {
                return Ok(LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::DefinitionProjection {
                        definition: definition.name.clone(),
                        expected_source: source_fact.clone(),
                        expected_target: inferred_fact.clone(),
                    },
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        fact_id: Some(source_fact_id),
                        proposition: source_fact.clone(),
                        proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                    }],
                });
            }
        }
    }
    if positive_real_membership_infers_strict_positivity(source_fact, inferred_fact) {
        if let Some(source_fact_id) = source_fact_id {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::PositiveRealMembership,
                ),
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    fact_id: Some(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                }],
            });
        }
    }
    if crate::litex_to_lean_ir::is_closed_numeric_relation(inferred_fact) {
        if let Some(target_set) =
            crate::litex_to_lean_ir::closed_compact_numeric_set_fact(source_fact)
        {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedNumericReflection { target_set },
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
    }
    Ok(LitexToLeanFactProofIr::Inference {
        source_fact_id,
        reason: reason.to_string(),
    })
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

fn object_type_fact_for_litex_to_lean(
    obj: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
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
            litex_to_lean_ir_error(
                &expected.line_file(),
                format!(
                    "{} `{}` reached Litex-to-Lean without a FactId",
                    context, expected
                ),
            )
        })
}

fn added_fact_id_from_infer_result(
    infer_result: &InferResult,
    expected: &Fact,
    context: &str,
) -> Result<FactId, RuntimeError> {
    let expected_text = expected.to_string();
    for output in infer_result.store_fact_outputs.iter() {
        if output.itself_and_why_itself_is_stored.0.to_string() == expected_text {
            if let Some(fact_id) = output.fact_id {
                return Ok(fact_id);
            }
        }
        for (fact, fact_id) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
        {
            if fact.to_string() == expected_text {
                if let Some(fact_id) = fact_id {
                    return Ok(*fact_id);
                }
            }
        }
    }
    Err(litex_to_lean_ir_error(
        &expected.line_file(),
        format!(
            "{} `{}` reached Litex-to-Lean without a FactId",
            context, expected
        ),
    ))
}

fn build_litex_to_lean_ir_contradiction_results(
    runtime: &Runtime,
    results: &[StmtResult],
    impossible_fact: &AtomicFact,
    context: &LitexToLeanIrConstructionContext,
) -> Result<LitexToLeanContradictionIr, RuntimeError> {
    if results.len() != 2 {
        return Err(litex_to_lean_ir_error(
            &impossible_fact.line_file(),
            "a contradiction must retain exactly the named fact and its logical negation",
        ));
    }
    let expected_fact: Fact = impossible_fact.clone().into();
    let expected_negation: Fact = impossible_fact.logical_negation()?.into();
    let mut fact =
        runtime.build_litex_to_lean_ir_fact_from_result(&results[0], "impossible fact", context)?;
    let mut negated_fact = runtime.build_litex_to_lean_ir_fact_from_result(
        &results[1],
        "negated impossible fact",
        context,
    )?;
    if fact.proposition.to_string() != expected_fact.to_string()
        || negated_fact.proposition.to_string() != expected_negation.to_string()
    {
        return Err(litex_to_lean_ir_error(
            &impossible_fact.line_file(),
            "retained contradiction checks do not match the named impossible fact",
        ));
    }
    fact.fact_id = None;
    negated_fact.fact_id = None;
    Ok(LitexToLeanContradictionIr {
        fact: Box::new(fact),
        negated_fact: Box::new(negated_fact),
    })
}

fn build_litex_to_lean_ir_parameter_group(
    group: &ParamGroupWithParamType,
) -> Result<LitexToLeanParameterGroupIr, RuntimeError> {
    let Some(_) = group.params.first() else {
        return Err(litex_to_lean_ir_error(
            &default_line_file(),
            "Litex-to-Lean cannot lower an empty parameter group",
        ));
    };
    Ok(LitexToLeanParameterGroupIr {
        symbol_ids: group.params.iter().map(|binding| binding.id()).collect(),
        names: group
            .params
            .iter()
            .map(|binding| binding.name().to_string())
            .collect(),
        param_type: build_litex_to_lean_ir_parameter_type(&group.param_type)?,
    })
}

fn build_litex_to_lean_ir_parameter_type(
    param_type: &ParamType,
) -> Result<LitexToLeanParameterTypeIr, RuntimeError> {
    match param_type {
        ParamType::Set(_) => Ok(LitexToLeanParameterTypeIr::Set),
        ParamType::NonemptySet(_) => Ok(LitexToLeanParameterTypeIr::NonemptySet),
        ParamType::FiniteSet(_) => Ok(LitexToLeanParameterTypeIr::FiniteSet),
        ParamType::Obj(obj) => {
            let set = LitexToLeanObjectIr::lower(obj)
                .map_err(|message| litex_to_lean_ir_error(&default_line_file(), message))?;
            Ok(LitexToLeanParameterTypeIr::MemberOf { set })
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

fn ensure_fact_objects_supported_by_litex_to_lean_ir(fact: &Fact) -> Result<(), RuntimeError> {
    let mut objects = Vec::new();
    collect_fact_objects_for_litex_to_lean(fact, &mut objects);
    for object in objects {
        LitexToLeanObjectIr::lower(object)
            .map_err(|message| litex_to_lean_ir_error(&fact.line_file(), message))?;
    }
    Ok(())
}

fn collect_fact_objects_for_litex_to_lean<'a>(fact: &'a Fact, objects: &mut Vec<&'a Obj>) {
    match fact {
        Fact::AtomicFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ForallFact(fact) => collect_forall_objects_for_litex_to_lean(fact, objects),
        Fact::ForallFactWithIff(fact) => {
            collect_forall_objects_for_litex_to_lean(&fact.forall_fact, objects);
            for iff_fact in fact.iff_facts.iter() {
                collect_forall_conclusion_objects_for_litex_to_lean(iff_fact, objects);
            }
        }
        Fact::NotForall(fact) => {
            collect_forall_objects_for_litex_to_lean(&fact.forall_fact, objects)
        }
    }
}

fn collect_forall_objects_for_litex_to_lean<'a>(fact: &'a ForallFact, objects: &mut Vec<&'a Obj>) {
    for group in fact.params_def_with_type.groups.iter() {
        if let ParamType::Obj(set) = &group.param_type {
            objects.push(set);
        }
    }
    for premise in fact.dom_facts.iter() {
        collect_fact_objects_for_litex_to_lean(premise, objects);
    }
    for conclusion in fact.then_facts.iter() {
        collect_forall_conclusion_objects_for_litex_to_lean(conclusion, objects);
    }
}

fn collect_forall_conclusion_objects_for_litex_to_lean<'a>(
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

fn fact_uses_only_forall_params(
    fact: &LitexToLeanFactIr,
    retained_names: &HashSet<String>,
) -> bool {
    let mut objects = Vec::new();
    collect_fact_objects_for_litex_to_lean(&fact.proposition, &mut objects);
    objects
        .into_iter()
        .flat_map(Obj::collect_forall_free_param_names)
        .all(|name| retained_names.contains(&name))
}

fn litex_to_lean_ir_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}
