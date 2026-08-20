use crate::litex_to_lean_ir::{
    LitexToLeanCaseBranchConclusionIr, LitexToLeanRegisteredRuleApplicationIr,
    LitexToLeanTypedBoundObjectIr,
};
use crate::prelude::*;
use crate::verify::local_builtin_catalog::registered_local_builtin_rules;
use crate::verify::rule_schema::{
    canonical_atomic_facts_equal, canonical_objs_equal, canonical_quantifier_free_facts_equal,
    match_conclusion, MatchLimits,
};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
struct LitexToLeanIrConstructionContext {
    local_fact_ids: HashMap<String, FactId>,
    fact_id_aliases: HashMap<FactId, FactId>,
}

impl LitexToLeanIrConstructionContext {
    fn with_infer_result(&self, infer_result: &SuccessInferResult) -> Self {
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

pub struct LitexToLeanIrBuilder {
    /// Stateless substitution/instantiation utility. This is deliberately a
    /// fresh runtime with no executed environment; semantic evidence must
    /// come from the recursive `StmtResult` passed to `compile_statement`.
    instantiator: Runtime,
}

impl LitexToLeanIrBuilder {
    pub fn new() -> Self {
        Self {
            instantiator: Runtime::new(),
        }
    }
}

impl LitexToLeanIrBuilder {
    pub fn compile_statement(
        &self,
        result: &StmtResult,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        if let Some(success) = result.factual_success() {
            return Ok(LitexToLeanStatementIr::Fact(
                self.compile_fact_stmt_result(success)?,
            ));
        }

        let Some(success) = result.non_factual_success() else {
            return Err(litex_to_lean_ir_error(
                &result.line_file(),
                "Litex-to-Lean IR requires a successful statement result",
            ));
        };
        match success {
            SuccessStmtResult::DefPredicateStmt(
                SuccessDefPredicateStmtResult::DefAbstractPropStmt(result),
            ) => Ok(
                LitexToLeanStatementIr::DefPredicateStmt(
                    LitexToLeanDefPredicateStmtIr::DefAbstractPropStmt(
                        LitexToLeanDefAbstractPropStmtIr {
                            name: result.statement.name.clone(),
                            params: result.statement.params.clone(),
                        },
                    ),
                ),
            ),
            SuccessStmtResult::DefPredicateStmt(
                SuccessDefPredicateStmtResult::DefPropStmt(result),
            ) => {
                let stmt = &result.statement;
                for fact in stmt.iff_facts.iter() {
                    ensure_fact_objects_supported_by_litex_to_lean_ir(fact)?;
                }
                Ok(LitexToLeanStatementIr::DefPredicateStmt(
                    LitexToLeanDefPredicateStmtIr::DefPropStmt(LitexToLeanDefPropStmtIr {
                        name: stmt.name.clone(),
                        params: stmt
                            .params_def_with_type
                            .groups
                            .iter()
                            .map(build_litex_to_lean_ir_parameter_group)
                            .collect::<Result<Vec<_>, RuntimeError>>()?,
                        iff_facts: stmt.iff_facts.clone(),
                    }),
                ))
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::LetObjStmt(result)) => {
                self.build_litex_to_lean_ir_let_object_statement(&result.statement, &result.common)
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveObjEqualStmt(result)) => {
                self.build_litex_to_lean_ir_have_object_equal_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveFnEqualStmt(result)) => {
                self.build_litex_to_lean_ir_have_function_equal_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveTupleStmt(result)) => {
                self.build_litex_to_lean_ir_have_tuple_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::DefObjStmt(
                SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(result),
            ) => {
                self.build_litex_to_lean_ir_have_object_choice_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::ObtainObjFromExistFact(
                result,
            )) => {
                let (source, witnesses, projections) = self
                    .build_litex_to_lean_ir_existential_witness(
                        &result.statement.equal_tos,
                        &result.statement.line_file,
                        &result.common,
                        result.verification.as_ref(),
                    )?;
                Ok(LitexToLeanStatementIr::DefObjStmt(
                    LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(
                        LitexToLeanObtainObjFromExistFactIr {
                            source,
                            witnesses,
                            projections,
                        },
                    ),
                ))
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::ObtainObjFromAtomicFact(
                result,
            )) => {
                let (source, witnesses, projections) = self
                    .build_litex_to_lean_ir_existential_witness(
                        &result.statement.equal_tos,
                        &result.statement.line_file,
                        &result.common,
                        result.verification.as_ref(),
                    )?;
                Ok(LitexToLeanStatementIr::DefObjStmt(
                    LitexToLeanDefObjStmtIr::ObtainObjFromAtomicFact(
                        LitexToLeanObtainObjFromAtomicFactIr {
                            source,
                            witnesses,
                            projections,
                        },
                    ),
                ))
            }
            SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::ObtainObjFromThm(result)) => Err(
                litex_to_lean_ir_error(
                    &result.statement.line_file,
                    "Litex-to-Lean does not yet support theorem-backed `obtain`; use an explicit theorem application followed by existential elimination",
                ),
            ),
            SuccessStmtResult::DefObjStmt(
                SuccessDefObjStmtResult::HaveObjByExistFactsStmt(result),
            ) => {
                let (source, witnesses, projections) = self
                    .build_litex_to_lean_ir_existential_witness(
                        &result.statement.param_def.collect_param_bindings(),
                        &result.statement.line_file,
                        &result.common,
                        result.verification.as_ref(),
                    )?;
                Ok(LitexToLeanStatementIr::DefObjStmt(
                    LitexToLeanDefObjStmtIr::HaveObjByExistFactsStmt(
                        LitexToLeanHaveObjByExistFactsStmtIr {
                            source,
                            witnesses,
                            projections,
                        },
                    ),
                ))
            }
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessExistFact(result)) => {
                self.build_litex_to_lean_ir_witness_exist_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessAtomicFact(result)) => {
                self.build_litex_to_lean_ir_witness_atomic_fact_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(result)) => {
                self.build_litex_to_lean_ir_by_cases_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(result)) => {
                self.build_litex_to_lean_ir_by_contra_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(result)) => {
                self.build_litex_to_lean_ir_by_definition_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ExampleStmt(result)) => {
                self.build_litex_to_lean_ir_example_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result)) => {
                self.build_litex_to_lean_ir_claim_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::SketchStmt(result)) => {
                self.build_litex_to_lean_ir_sketch_statement(
                    &result.statement,
                    &result.common,
                    result.proof.as_ref(),
                )
            }
            SuccessStmtResult::Command(SuccessCommandStmtResult::DoNothingStmt(result)) => {
                if !result.common.infers.is_empty() {
                    return Err(litex_to_lean_ir_error(
                        &result.statement.line_file,
                        "`do_nothing` unexpectedly changed the environment or retained proof results",
                    ));
                }
                Ok(LitexToLeanStatementIr::Command(
                    LitexToLeanCommandStmtIr::DoNothingStmt(LitexToLeanDoNothingStmtIr::new(
                        result.statement.line_file.clone(),
                    )),
                ))
            }
            SuccessStmtResult::DefThmStmt(result) => {
                self.build_litex_to_lean_ir_named_theorem_statement(
                    &result.statement,
                    &result.common,
                    result.verification.as_ref(),
                )
            }
            SuccessStmtResult::AxiomStmt(result) => Err(litex_to_lean_ir_error(
                &result.statement.line_file,
                "Litex-to-Lean does not compile explicit `axiom` declarations",
            )),
            SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustStmt(result)) => {
                let stmt = &result.statement;
                let common = &result.common;
                let excluded = stmt
                    .facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<HashSet<_>>();
                let mut facts = Vec::with_capacity(stmt.facts.len());
                for fact in stmt.facts.iter() {
                    ensure_fact_objects_supported_by_litex_to_lean_ir(fact)?;
                    facts.push(LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(
                            stored_fact_id_from_infer_result(
                                &common.infers,
                                fact,
                                "trusted fact",
                            )?,
                        ),
                        proposition: fact.clone(),
                        proof: LitexToLeanFactProofIr::Trusted,
                    });
                }
                Ok(LitexToLeanStatementIr::UnsafeStmt(
                    LitexToLeanUnsafeStmtIr::TrustStmt(LitexToLeanTrustStmtIr {
                        facts,
                        inferred_facts: self
                            .build_litex_to_lean_ir_inferred_facts(&common.infers, &excluded)?,
                    }),
                ))
            }
            other => {
                let statement = other.statement();
                Err(litex_to_lean_ir_error(
                &statement.line_file(),
                format!(
                    "Litex-to-Lean IR MVP does not support statement kind `{}`",
                    statement.stmt_type_name()
                ),
            ))}
        }
    }

    /// Transitional fact-family adapter used while the statement-level IR is
    /// being removed. It deliberately returns only the payload needed by the
    /// fact renderer, never a second top-level statement enum.
    pub(crate) fn compile_fact_stmt_result(
        &self,
        success: &SuccessFactStmtResult,
    ) -> Result<LitexToLeanFactStatementIr, RuntimeError> {
        let source_fact = success.fact();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&source_fact)?;
        let fact = self.build_litex_to_lean_ir_fact_from_success(success)?;
        let well_definedness_context = self.well_definedness_context_for_factual_success(success);
        let excluded = HashSet::from([source_fact.to_string()]);
        if success.fact_id.is_none() {
            let projected =
                self.build_litex_to_lean_ir_projected_forall_statement(success, fact, excluded)?;
            let LitexToLeanStatementIr::Fact(projected) = projected else {
                unreachable!("forall projection builder always returns a fact statement")
            };
            return Ok(projected);
        }
        let recursive_well_definedness =
            crate::result::project_compositional_well_definedness(&success.well_definedness)
                .map_err(|message| litex_to_lean_ir_error(&source_fact.line_file(), message))?;
        Ok(LitexToLeanFactStatementIr {
            source: fact,
            stored_projections: Vec::new(),
            inferred_facts: self
                .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
            well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                &recursive_well_definedness,
                &well_definedness_context,
            )?,
        })
    }

    /// Transitional nested-proof adapter. Unlike a statement compilation, a
    /// verifier child Result is intentionally anonymous and therefore has no
    /// stored FactId. The StmtResult-to-Lean compiler uses this only until the
    /// remaining fact-proof renderers consume `SuccessFactProofResult`
    /// directly.
    pub(crate) fn compile_nested_fact_result_without_requiring_storage(
        &self,
        success: &SuccessFactStmtResult,
    ) -> Result<(LitexToLeanFactIr, LitexToLeanWellDefinednessCertificateIr), RuntimeError> {
        let source_fact = success.fact();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&source_fact)?;
        let fact = self.build_litex_to_lean_ir_fact_from_success(success)?;
        let well_definedness_context = self.well_definedness_context_for_factual_success(success);
        let recursive_well_definedness = if success.well_definedness.recursive.is_some() {
            crate::result::project_compositional_well_definedness(&success.well_definedness)
                .map_err(|message| litex_to_lean_ir_error(&source_fact.line_file(), message))?
        } else {
            // A nested verification-only fact predates compositional WD
            // capture. Its parent statement owns the value's WD stage; this
            // compatibility proof adapter therefore has no separate object
            // certificate to project.
            WellDefinednessCertificate::default()
        };
        let well_definedness = self.build_litex_to_lean_ir_well_definedness_certificate(
            &recursive_well_definedness,
            &well_definedness_context,
        )?;
        Ok((fact, well_definedness))
    }

    fn build_litex_to_lean_ir_let_object_statement(
        &self,
        stmt: &LetObjStmt,
        success: &SuccessStmtCommonResult,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let name = stmt.symbol_binding.name().to_string();
        let defined_obj: Obj =
            Identifier::new_bound(name.clone(), stmt.symbol_binding.as_ref()).into();
        let defining_equality: Fact =
            EqualFact::new(defined_obj, stmt.value.clone(), stmt.line_file.clone()).into();
        let defining_equality_id = stored_fact_id_from_infer_result(
            &success.infers,
            &defining_equality,
            "let-object defining equality",
        )?;
        let value = LitexToLeanObjectIr::lower(&stmt.value)
            .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let defining_equality_ir = LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(defining_equality_id),
            proposition: defining_equality.clone(),
            proof: LitexToLeanFactProofIr::ObjectDefinitionEquality,
        };
        let excluded = HashSet::from([defining_equality.to_string()]);
        let context = LitexToLeanIrConstructionContext::default();
        Ok(LitexToLeanStatementIr::DefObjStmt(
            LitexToLeanDefObjStmtIr::LetObjStmt(LitexToLeanLetObjStmtIr::new(
                stmt.line_file.clone(),
                stmt.symbol_binding.id(),
                name,
                value,
                defining_equality_ir,
                self.build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &context,
                )?,
            )),
        ))
    }

    fn build_litex_to_lean_ir_have_function_equal_statement(
        &self,
        stmt: &HaveFnEqualStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyFunctionDefinitionResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "function definition has no structured body-to-environment verification result",
            ));
        };
        let source_return_set = stmt.equal_to_anonymous_fn.body.ret_set.as_ref().clone();

        let function_set = FnSet::from_body(stmt.equal_to_anonymous_fn.body.clone())?;
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
            &verification.return_check,
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
        return_check.make_anonymous();

        let expected_membership = verification.function_membership.clone();
        let expected_equality = verification.defining_equality.clone();
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

        Ok(LitexToLeanStatementIr::DefObjStmt(
            LitexToLeanDefObjStmtIr::HaveFnEqualStmt(LitexToLeanHaveFnEqualStmtIr {
                symbol_id: stmt.symbol_binding.id(),
                name: stmt.name().to_string(),
                function,
                source_body,
                body,
                parameter_premises,
                domain_premises,
                inferred_premises,
                return_check,
                membership: LitexToLeanStoredFunctionFactIr {
                    fact_id: membership_id,
                    proposition: expected_membership,
                },
                defining_equality: LitexToLeanStoredFunctionFactIr {
                    fact_id: equality_id,
                    proposition: expected_equality,
                },
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &assumption_context,
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_have_tuple_statement(
        &self,
        stmt: &HaveTupleStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyTupleOrCartDimensionResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "indexed tuple must retain its positive-dimension and at-least-two checks",
            ));
        };
        let mut dimension_checks = Vec::with_capacity(2);
        for result in [
            verification.positive_check.as_ref(),
            verification.at_least_two_check.as_ref(),
        ] {
            let mut check = self.build_litex_to_lean_ir_fact_from_result(
                result,
                "indexed tuple dimension check",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            check.make_anonymous();
            dimension_checks.push(check);
        }

        let target: Obj =
            Identifier::new_bound(stmt.name().to_string(), stmt.symbol_binding.as_ref()).into();
        let expected_is_tuple: Fact =
            IsTupleFact::new(target.clone(), stmt.line_file.clone()).into();
        let expected_dimension: Fact = EqualFact::new(
            TupleDim::new(target.clone()).into(),
            stmt.dimension.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let mut stored_facts = Vec::with_capacity(3);
        for (expected, role) in [
            (
                &expected_is_tuple,
                LitexToLeanStoredTupleFactRoleIr::IsTuple,
            ),
            (
                &expected_dimension,
                LitexToLeanStoredTupleFactRoleIr::Dimension,
            ),
        ] {
            stored_facts.push(LitexToLeanStoredTupleFactIr {
                fact_id: stored_fact_id_from_infer_result(
                    &success.infers,
                    expected,
                    "indexed tuple stored fact",
                )?,
                proposition: expected.clone(),
                role,
            });
        }
        let coordinate_outputs = success
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                let Fact::ForallFact(forall) = &output.itself_and_why_itself_is_stored.0 else {
                    return false;
                };
                if forall.params_def_with_type.number_of_params() != 1
                    || !forall.dom_facts.is_empty()
                    || forall.then_facts.len() != 1
                {
                    return false;
                }
                let Fact::AtomicFact(AtomicFact::EqualFact(equality)) =
                    forall.then_facts[0].clone().to_fact()
                else {
                    return false;
                };
                matches!(
                    &equality.left,
                    Obj::ObjAtIndex(access)
                        if obj_equality_key(access.obj.as_ref()) == obj_equality_key(&target)
                )
            })
            .collect::<Vec<_>>();
        if coordinate_outputs.len() != 1 {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "indexed tuple did not retain exactly one coordinate forall effect",
            ));
        }
        let coordinate = coordinate_outputs[0];
        stored_facts.push(LitexToLeanStoredTupleFactIr {
            fact_id: coordinate.fact_id.ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "indexed tuple coordinate forall has no stable FactId",
                )
            })?,
            proposition: coordinate.itself_and_why_itself_is_stored.0.clone(),
            role: LitexToLeanStoredTupleFactRoleIr::Coordinate,
        });

        Ok(LitexToLeanStatementIr::DefObjStmt(
            LitexToLeanDefObjStmtIr::HaveTupleStmt(LitexToLeanHaveTupleStmtIr {
                symbol_id: stmt.symbol_binding.id(),
                name: stmt.name().to_string(),
                index_symbol_id: stmt.index_binding.id(),
                index_name: stmt.index_name().to_string(),
                dimension: LitexToLeanObjectIr::lower(&stmt.dimension)
                    .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?,
                value: LitexToLeanObjectIr::lower(&stmt.value)
                    .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?,
                dimension_checks,
                stored_facts,
            }),
        ))
    }

    fn build_litex_to_lean_ir_witness_exist_statement(
        &self,
        stmt: &WitnessExistFact,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyWitnessExistResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
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
        let fact =
            self.build_litex_to_lean_ir_exist_introduction_fact(stmt, verification, Some(fact_id))?;

        Ok(LitexToLeanStatementIr::Witness(
            LitexToLeanWitnessStmtIr::WitnessExistFact(LitexToLeanWitnessExistFactIr {
                facts: vec![fact],
                inferred_facts: Vec::new(),
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &LitexToLeanIrConstructionContext::default().with_infer_result(&success.infers),
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_exist_introduction_fact(
        &self,
        stmt: &WitnessExistFact,
        verification: &SuccessVerifyWitnessExistResult,
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
            || stmt.exist_fact_in_witness.facts().len() != verification.body_checks.len()
            || verification.proof_steps.len() != stmt.proof.len()
            || verification.uniqueness_check.is_some()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "existential witness evidence has inconsistent parameter, proof-step, body, or uniqueness mappings",
            ));
        }

        let existential: Fact = stmt.exist_fact_in_witness.clone().into();
        ensure_fact_objects_supported_by_litex_to_lean_ir(&existential)?;

        let proof_steps = verification
            .proof_steps
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;

        let instantiated_types = self.instantiator.inst_param_def_with_type_one_by_one(
            param_defs,
            &stmt.equal_tos,
            ParamObjType::Exist,
        )?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let mut parameter_requirements = Vec::new();
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
            requirement.make_anonymous();
            parameter_requirements.push(requirement);
        }

        let param_to_obj_map =
            param_defs.param_defs_and_args_to_param_to_arg_map(stmt.equal_tos.as_slice());
        let mut body_premises = Vec::with_capacity(stmt.exist_fact_in_witness.facts().len());
        for (body_index, (body, result)) in stmt
            .exist_fact_in_witness
            .facts()
            .iter()
            .zip(verification.body_checks.iter())
            .enumerate()
        {
            let expected = self
                .instantiator
                .inst_quantifier_free_fact(body, &param_to_obj_map, ParamObjType::Exist, None)?
                .to_fact();
            let mut premise = self.build_litex_to_lean_ir_fact_from_result(
                result,
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
            premise.make_anonymous();
            body_premises.push(premise);
        }
        Ok(LitexToLeanFactIr {
            storage: fact_id.into(),
            proposition: existential,
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ExistIntroduction {
                    witnesses: stmt.equal_tos.clone(),
                    steps: proof_steps,
                },
                parameter_requirements,
                premises: body_premises,
            },
        })
    }

    fn build_litex_to_lean_ir_witness_atomic_fact_statement(
        &self,
        stmt: &WitnessAtomicFact,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyWitnessAtomicFactResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "atomic fact witness has no frozen definition-introduction verification result",
            ));
        };
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

        let reconstructed = self.instantiator.instantiate_existential_prop_definition(
            &stmt.atomic_fact,
            &verification.definition,
            &stmt.line_file,
        )?;
        if !reconstructed.is_plain_exist()
            || Runtime::exist_fact_normalized_body_string(&self.instantiator, &reconstructed)?
                != Runtime::exist_fact_normalized_body_string(
                    &self.instantiator,
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
            None,
        )?;
        let named_fact = LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(target_id),
            proposition: target.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DefinitionIntroduction,
                parameter_requirements: Vec::new(),
                premises: vec![existential_introduction],
            },
        };
        let projected_existential = LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(existential_id),
            proposition: existential.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DefinitionProjection,
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Stored(target_id),
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
        Ok(LitexToLeanStatementIr::Witness(
            LitexToLeanWitnessStmtIr::WitnessAtomicFact(LitexToLeanWitnessAtomicFactIr {
                facts: vec![named_fact],
                inferred_facts,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &LitexToLeanIrConstructionContext::default().with_infer_result(&success.infers),
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_existential_witness(
        &self,
        bindings: &[SymbolBinding],
        line_file: &LineFile,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyExistentialEliminationResult>,
    ) -> Result<
        (
            LitexToLeanFactIr,
            Vec<LitexToLeanExistentialWitnessIr>,
            Vec<LitexToLeanFactIr>,
        ),
        RuntimeError,
    > {
        let Some(verification) = verification else {
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
            &verification.source_result,
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
            || Runtime::exist_fact_normalized_body_string(&self.instantiator, source_exist_fact)?
                != Runtime::exist_fact_normalized_body_string(&self.instantiator, exist_fact)?
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
        source.make_anonymous();

        let witness_objs = bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect::<Vec<Obj>>();
        let instantiated_types = self.instantiator.inst_param_def_with_type_one_by_one(
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
                storage: LitexToLeanFactStorageIr::Stored(fact_id),
                proposition: expected.clone(),
                proof: LitexToLeanFactProofIr::ExistentialElimination {
                    role: LitexToLeanExistentialProjectionRoleIr::ParameterType { witness_index },
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
                .instantiator
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
                storage: LitexToLeanFactStorageIr::Stored(fact_id),
                proposition: expected.clone(),
                proof: LitexToLeanFactProofIr::ExistentialElimination {
                    role: LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index },
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

        Ok((source, witnesses, projections))
    }

    fn build_litex_to_lean_ir_have_object_choice_statement(
        &self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyObjectChoiceResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object choice has no structured nonemptiness-to-membership verification result",
            ));
        };
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if stmt.param_def.groups.len() != verification.groups.len() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object choice evidence has inconsistent parameter-group mappings",
            ));
        }
        let mut verified_items = Vec::with_capacity(bindings_with_types.len());
        for (param_group, verified_group) in
            stmt.param_def.groups.iter().zip(verification.groups.iter())
        {
            if param_group.params.len() != verified_group.selected_type_facts.len() {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "object choice evidence has inconsistent binding and type-fact mappings",
                ));
            }
            for selected_type_fact in &verified_group.selected_type_facts {
                verified_items.push((selected_type_fact, verified_group.nonempty_check.as_deref()));
            }
        }
        if bindings_with_types.len() != verified_items.len() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "object choice evidence has inconsistent flattened binding mappings",
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
            let (selected_type_fact, nonempty_check) = verified_items[index];
            let Some(check_result) = nonempty_check else {
                return Err(litex_to_lean_ir_error(
                    &stmt.line_file,
                    "object-carrier choice did not retain a nonemptiness proof",
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
            nonempty_proof.make_anonymous();

            let definition_name = binding.name().to_string();
            let defined_obj: Obj =
                Identifier::new_bound(definition_name.clone(), binding.as_ref()).into();
            let expected_membership =
                object_type_fact_for_litex_to_lean(defined_obj, param_type, stmt.line_file.clone());
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
                    storage: LitexToLeanFactStorageIr::Stored(membership_fact_id),
                    proposition: selected_type_fact.clone(),
                    proof: LitexToLeanFactProofIr::ObjectChoice,
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

        Ok(LitexToLeanStatementIr::DefObjStmt(
            LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(
                LitexToLeanHaveObjInNonemptySetOrParamTypeStmtIr { choices },
            ),
        ))
    }

    fn build_litex_to_lean_ir_have_object_equal_statement(
        &self,
        stmt: &HaveObjEqualStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyHaveObjEqualResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "have-object equality has no structured type-check result",
            ));
        };
        let bindings_with_types = stmt.param_def.collect_param_bindings_with_types();
        if bindings_with_types.len() != stmt.objs_equal_to.len()
            || bindings_with_types.len() != verification.type_checks.len()
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
                &verification.type_checks[index],
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
            value_check.make_anonymous();

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
                storage: LitexToLeanFactStorageIr::Stored(stored_type_fact_id),
                proposition: stored_type_fact,
                proof: LitexToLeanFactProofIr::ObjectDefinitionMembership {
                    value_check: Box::new(value_check),
                },
            });
            facts.push(LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Stored(stored_equality_fact_id),
                proposition: stored_equality,
                proof: LitexToLeanFactProofIr::ObjectDefinitionEquality,
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

        Ok(LitexToLeanStatementIr::DefObjStmt(
            LitexToLeanDefObjStmtIr::HaveObjEqualStmt(LitexToLeanHaveObjEqualStmtIr {
                definitions,
                facts,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &LitexToLeanIrConstructionContext::default(),
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_by_definition_statement(
        &self,
        stmt: &ByDefStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyByDefinitionResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
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
        let definition = verification.definition.as_ref().ok_or_else(|| {
            litex_to_lean_ir_error(
                &stmt.line_file,
                "by-definition result does not retain its concrete prop definition",
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
            || verification.clause_checks.len() != verification.definition_clause_facts.len()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-definition retained statement, clause, or result counts do not match",
            ));
        }
        let argument_verification =
            verification.argument_verification.as_ref().ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    "by-definition parameter checks were not retained",
                )
            })?;
        let proof = self.build_litex_to_lean_ir_definition_reduction(
            &target,
            &definition,
            &argument_verification.checks,
            &verification.definition_clause_facts,
            &verification.clause_checks,
            &LitexToLeanIrConstructionContext::default(),
        )?;
        let fact_id = stored_fact_id_from_infer_result(
            &success.infers,
            &target,
            "by-definition target fact",
        )?;
        let fact = LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(fact_id),
            proposition: target.clone(),
            proof,
        };
        let mut retained_child_facts = Vec::new();
        let mut retained_child_ids = HashSet::new();
        for child in argument_verification
            .checks
            .iter()
            .chain(verification.clause_checks.iter())
        {
            let child = self.build_litex_to_lean_ir_fact_from_result(
                child,
                "by-definition retained child fact",
                &LitexToLeanIrConstructionContext::default(),
            )?;
            let Some(child_id) = child.stored_fact_id() else {
                continue;
            };
            if child_id == fact_id || !retained_child_ids.insert(child_id) {
                continue;
            }
            if matches!(
                child.proof,
                LitexToLeanFactProofIr::KnownFactCitation { source_fact_id }
                    if source_fact_id == child_id
            ) {
                continue;
            }
            retained_child_facts.push(child);
        }
        Ok(LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(
            LitexToLeanByDefStmtIr {
                facts: vec![fact],
                inferred_facts: retained_child_facts,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &LitexToLeanIrConstructionContext::default().with_infer_result(&success.infers),
                )?,
            },
        )))
    }

    fn build_litex_to_lean_ir_by_cases_statement(
        &self,
        stmt: &ByCasesStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyByCasesResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-cases statement has no structured verification result",
            ));
        };
        if verification.goal_well_definedness.len() != verification.then_facts.len() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "by-cases did not retain one well-definedness result per exported goal",
            ));
        }
        let goal_well_definedness = crate::result::project_compositional_well_definedness_many(
            &verification.goal_well_definedness,
        )
        .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let mut coverage = self.build_litex_to_lean_ir_fact_from_result(
            &verification.coverage_check,
            "by-cases coverage",
            &LitexToLeanIrConstructionContext::default(),
        )?;
        coverage.make_anonymous();
        let cases = verification
            .branches
            .iter()
            .map(|branch| branch.assumption.clone())
            .collect::<Vec<_>>();
        let expected_coverage: Fact = OrFact::new(cases, stmt.line_file.clone()).into();
        if coverage.proposition.to_string() != expected_coverage.to_string() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                format!(
                    "by-cases coverage `{}` does not match cases `{}`",
                    coverage.proposition, expected_coverage
                ),
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
            let mut branches = Vec::with_capacity(verification.branches.len());
            for branch in &verification.branches {
                let case_fact: Fact = branch.assumption.clone().into();
                let mut case_context = LitexToLeanIrConstructionContext {
                    local_fact_ids: HashMap::from([(
                        case_fact.to_string(),
                        branch.assumption_fact_id,
                    )]),
                    ..LitexToLeanIrConstructionContext::default()
                }
                .with_infer_result(&branch.proof_scope.assumption_infers);
                for (fact_id, fact) in branch.proof_scope.assumption_components.iter() {
                    case_context
                        .local_fact_ids
                        .insert(fact.to_string(), *fact_id);
                }
                let steps = branch
                    .proof_steps
                    .iter()
                    .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let exit = match &branch.exit {
                    SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                        LitexToLeanCaseBranchExitIr::Contradiction(
                            build_litex_to_lean_ir_contradiction_pair(
                                self,
                                &result.contradiction.impossible_check,
                                &result.contradiction.negated_impossible_check,
                                &result.impossible_fact,
                                &case_context,
                            )?,
                        )
                    }
                    SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                        if result.checks.len() != verification.then_facts.len() {
                            return Err(litex_to_lean_ir_error(
                                &stmt.line_file,
                                "a by-cases branch does not retain one result per goal",
                            ));
                        }
                        let conclusion_result = &result.checks[goal_index];
                        let conclusion_success =
                            conclusion_result.factual_success().ok_or_else(|| {
                                litex_to_lean_ir_error(
                                    &stmt.line_file,
                                    "a by-cases branch conclusion is not a factual success",
                                )
                            })?;
                        let mut conclusion = self.build_litex_to_lean_ir_fact_from_result(
                            conclusion_result,
                            "by-cases branch conclusion",
                            &case_context,
                        )?;
                        if conclusion.proposition.to_string() != goal.to_string() {
                            return Err(litex_to_lean_ir_error(
                                &stmt.line_file,
                                "by-cases branch conclusion does not match its exported goal",
                            ));
                        }
                        conclusion.make_anonymous();
                        let recursive_well_definedness =
                            crate::result::project_compositional_well_definedness(
                                &conclusion_success.well_definedness,
                            )
                            .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
                        LitexToLeanCaseBranchExitIr::Conclusion(LitexToLeanCaseBranchConclusionIr {
                            fact: conclusion,
                            well_definedness: self
                                .build_litex_to_lean_ir_well_definedness_certificate(
                                    &recursive_well_definedness,
                                    &case_context,
                                )?,
                        })
                    }
                };
                let expected_components = match &branch.assumption {
                    AndChainAtomicFact::AtomicFact(_) => Vec::new(),
                    AndChainAtomicFact::AndFact(and_fact) => and_fact
                        .facts
                        .iter()
                        .cloned()
                        .map(Fact::from)
                        .collect::<Vec<_>>(),
                    AndChainAtomicFact::ChainFact(chain_fact) => chain_fact
                        .facts()?
                        .into_iter()
                        .map(Fact::from)
                        .collect::<Vec<_>>(),
                };
                let retained_components = &branch.proof_scope.assumption_components;
                if expected_components.len() != retained_components.len() {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "by-cases scope lost a structural assumption component",
                    ));
                }
                let mut assumption_inferred_facts = Vec::new();
                for (component_index, ((fact_id, retained), expected)) in retained_components
                    .iter()
                    .zip(expected_components.iter())
                    .enumerate()
                {
                    if retained.to_string() != expected.to_string() {
                        return Err(litex_to_lean_ir_error(
                            &retained.line_file(),
                            "by-cases structural assumption component changed position",
                        ));
                    }
                    assumption_inferred_facts.push(LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(*fact_id),
                        proposition: retained.clone(),
                        proof: LitexToLeanFactProofIr::RuleApplication {
                            rule: LitexToLeanProofRuleIr::ConjunctionProjection {
                                index: component_index,
                            },
                            parameter_requirements: Vec::new(),
                            premises: vec![LitexToLeanFactIr {
                                storage: LitexToLeanFactStorageIr::Stored(
                                    branch.assumption_fact_id,
                                ),
                                proposition: case_fact.clone(),
                                proof: LitexToLeanFactProofIr::KnownFactCitation {
                                    source_fact_id: branch.assumption_fact_id,
                                },
                            }],
                        },
                    });
                }
                let mut excluded_assumption_facts = HashSet::from([branch.assumption.to_string()]);
                excluded_assumption_facts
                    .extend(expected_components.iter().map(ToString::to_string));
                assumption_inferred_facts.extend(self.build_litex_to_lean_ir_inferred_facts(
                    &branch.proof_scope.assumption_infers,
                    &excluded_assumption_facts,
                )?);
                branches.push(LitexToLeanCaseBranchIr {
                    assumption: LitexToLeanLocalPremiseIr::new(
                        branch.assumption_fact_id,
                        case_fact,
                    ),
                    block: LitexToLeanLocalProofBlockIr {
                        premise_aliases: Vec::new(),
                        assumption_inferred_facts,
                        well_definedness: self
                            .build_litex_to_lean_ir_well_definedness_certificate(
                                &WellDefinednessCertificate::default(),
                                &case_context,
                            )?,
                        steps,
                    },
                    exit,
                });
            }

            facts.push(LitexToLeanFactIr {
                storage: explicit_proof_result_storage(&success.infers, goal),
                proposition: goal.clone(),
                proof: LitexToLeanFactProofIr::CaseSplit {
                    coverage: Box::new(coverage.clone()),
                    branches,
                },
            });
        }

        Ok(LitexToLeanStatementIr::By(
            LitexToLeanByStmtIr::ByCasesStmt(LitexToLeanByCasesStmtIr {
                facts,
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &explicit_keys)?,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &goal_well_definedness,
                    &LitexToLeanIrConstructionContext::default().with_infer_result(&success.infers),
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_by_contra_statement(
        &self,
        stmt: &ByContraStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyByContraResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let Some(verification) = verification else {
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
        if verification.proof_steps.len() != stmt.proof.len() {
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
            ..LitexToLeanIrConstructionContext::default()
        }
        .with_infer_result(&verification.proof_scope.assumption_infers);
        let steps = verification
            .proof_steps
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let contradiction = build_litex_to_lean_ir_contradiction_pair(
            self,
            &verification.contradiction.impossible_check,
            &verification.contradiction.negated_impossible_check,
            &verification.impossible_fact,
            &reverse_context,
        )?;
        let explicit_keys = HashSet::from([stmt.to_prove.to_string()]);
        let fact = LitexToLeanFactIr {
            storage: explicit_proof_result_storage(&success.infers, &stmt.to_prove),
            proposition: stmt.to_prove.clone(),
            proof: LitexToLeanFactProofIr::ByContradiction {
                reverse_assumption: LitexToLeanReverseAssumptionIr {
                    premise: LitexToLeanLocalPremiseIr::new(
                        verification.reverse_assumption_fact_id,
                        verification.reverse_assumption.clone(),
                    ),
                    introduction: reverse_assumption_introduction_for_target(&stmt.to_prove),
                },
                block: LitexToLeanLocalProofBlockIr {
                    premise_aliases: Vec::new(),
                    assumption_inferred_facts: self.build_litex_to_lean_ir_inferred_facts(
                        &verification.proof_scope.assumption_infers,
                        &HashSet::from([verification.reverse_assumption.to_string()]),
                    )?,
                    well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                        &WellDefinednessCertificate::default(),
                        &reverse_context,
                    )?,
                    steps,
                },
                contradiction,
            },
        };

        Ok(LitexToLeanStatementIr::By(
            LitexToLeanByStmtIr::ByContraStmt(LitexToLeanByContraStmtIr {
                facts: vec![fact],
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &explicit_keys)?,
                well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &LitexToLeanIrConstructionContext::default().with_infer_result(&success.infers),
                )?,
            }),
        ))
    }

    fn build_litex_to_lean_ir_nested_statement(
        &self,
        result: &StmtResult,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        self.compile_statement(result)
    }

    fn build_litex_to_lean_ir_claim_statement(
        &self,
        stmt: &ClaimStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyClaimResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let verification = verification.ok_or_else(|| {
            litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified `claim` reached Litex-to-Lean without goal proof evidence",
            )
        })?;
        let SuccessVerifyClaimResult::Fact(verification) = verification else {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "this simple `claim` tranche supports ordinary fact goals, not `forall` goals",
            ));
        };
        let scope = &verification.proof_scope;
        if verification.fact.to_string() != stmt.fact.to_string()
            || verification.proof_steps.len() != stmt.proof.len()
            || !scope.assumption_infers.is_empty()
            || !scope.assumption_components.is_empty()
        {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "`claim` proof-scope evidence does not match its source goal or result order",
            ));
        }
        ensure_fact_objects_supported_by_litex_to_lean_ir(&verification.fact)?;
        let target_fact_id = success
            .infers
            .store_fact_outputs
            .iter()
            .find(|output| {
                output.itself_and_why_itself_is_stored.0.to_string()
                    == verification.fact.to_string()
            })
            .and_then(|output| output.fact_id)
            .ok_or_else(|| {
                litex_to_lean_ir_error(
                    &stmt.line_file,
                    format!(
                        "claim target fact `{}` reached Litex-to-Lean without a FactId",
                        verification.fact
                    ),
                )
            })?;
        let context = LitexToLeanIrConstructionContext::default();
        let recursive_well_definedness =
            crate::result::project_compositional_well_definedness(&verification.well_definedness)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let well_definedness = self.build_litex_to_lean_ir_well_definedness_certificate(
            &recursive_well_definedness,
            &context,
        )?;
        let steps = verification
            .proof_steps
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let conclusion_result = verification.conclusion_check.as_ref();
        if conclusion_result.factual_success().is_none() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "`claim` goal verification did not retain a factual conclusion",
            ));
        }
        let mut target = self.build_litex_to_lean_ir_fact_from_result(
            conclusion_result,
            "claim conclusion",
            &context,
        )?;
        if target.proposition.to_string() != verification.fact.to_string() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "`claim` conclusion changed the checked source goal",
            ));
        }
        target.store_as(target_fact_id);
        let block = LitexToLeanLocalProofBlockIr {
            premise_aliases: Vec::new(),
            assumption_inferred_facts: Vec::new(),
            well_definedness: well_definedness.clone(),
            steps,
        };
        let excluded = HashSet::from([verification.fact.to_string()]);
        Ok(LitexToLeanStatementIr::ProofBlock(
            LitexToLeanProofBlockStmtIr::ClaimStmt(LitexToLeanClaimStmtIr::new(
                stmt.line_file.clone(),
                target,
                block,
                self.build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                well_definedness,
            )),
        ))
    }

    fn build_litex_to_lean_ir_example_statement(
        &self,
        stmt: &ExampleStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyClaimResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        if !success.infers.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "an `example` unexpectedly exported facts to the surrounding environment",
            ));
        }
        let verification = verification.ok_or_else(|| {
            litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified `example` reached Litex-to-Lean without goal proof evidence",
            )
        })?;
        let (target, mut block, context) = match verification {
            SuccessVerifyClaimResult::Fact(verification) => {
                let scope = &verification.proof_scope;
                if verification.fact.to_string() != stmt.fact.to_string()
                    || verification.proof_steps.len() != stmt.proof.len()
                    || !scope.assumption_infers.is_empty()
                    || !scope.assumption_components.is_empty()
                {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "`example` proof-scope evidence does not match its source goal or result order",
                    ));
                }
                ensure_fact_objects_supported_by_litex_to_lean_ir(&verification.fact)?;
                let context = LitexToLeanIrConstructionContext::default();
                let steps = verification
                    .proof_steps
                    .iter()
                    .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let conclusion_result = verification.conclusion_check.as_ref();
                if conclusion_result.factual_success().is_none() {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "`example` goal verification did not retain a factual conclusion",
                    ));
                }
                let mut target = self.build_litex_to_lean_ir_fact_from_result(
                    conclusion_result,
                    "example conclusion",
                    &context,
                )?;
                if target.proposition.to_string() != verification.fact.to_string() {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "`example` conclusion changed the checked source goal",
                    ));
                }
                target.make_anonymous();
                let block = LitexToLeanLocalProofBlockIr {
                    premise_aliases: Vec::new(),
                    assumption_inferred_facts: Vec::new(),
                    well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                        &WellDefinednessCertificate::default(),
                        &context,
                    )?,
                    steps,
                };
                (target, block, context)
            }
            SuccessVerifyClaimResult::Forall(verification) => {
                let proposition: Fact = verification.forall_fact.clone().into();
                let scope = &verification.proof_scope;
                if proposition.to_string() != stmt.fact.to_string()
                    || verification.proof_steps.len() != stmt.proof.len()
                    || verification.conclusion_checks.len()
                        != verification.forall_fact.then_facts.len()
                    || !scope.assumption_components.is_empty()
                {
                    return Err(litex_to_lean_ir_error(
                        &stmt.line_file,
                        "forall `example` proof-scope evidence does not match its source goal or result order",
                    ));
                }
                ensure_fact_objects_supported_by_litex_to_lean_ir(&proposition)?;

                let parameter_reason = InferReason::ParameterDefinition.store_reason();
                let parameter_premises = verification
                    .proof_scope
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| {
                        output.itself_and_why_itself_is_stored.1 == parameter_reason
                    })
                    .map(|output| {
                        let fact = output.itself_and_why_itself_is_stored.0.clone();
                        let fact_id = output.fact_id.ok_or_else(|| {
                            litex_to_lean_ir_error(
                                &fact.line_file(),
                                "an `example` parameter premise reached Litex-to-Lean without a FactId",
                            )
                        })?;
                        Ok(LitexToLeanLocalPremiseIr::new(fact_id, fact))
                    })
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let mut premises = Vec::with_capacity(verification.forall_fact.dom_facts.len());
                for dom_fact in verification.forall_fact.dom_facts.iter() {
                    let fact_id = verification
                        .proof_scope
                        .assumption_infers
                        .store_fact_outputs
                        .iter()
                        .find(|output| {
                            output.itself_and_why_itself_is_stored.0.to_string()
                                == dom_fact.to_string()
                        })
                        .and_then(|output| output.fact_id)
                        .ok_or_else(|| {
                            litex_to_lean_ir_error(
                                &dom_fact.line_file(),
                                "an `example` domain premise reached Litex-to-Lean without a FactId",
                            )
                        })?;
                    premises.push(LitexToLeanLocalPremiseIr::new(fact_id, dom_fact.clone()));
                }
                let inferred_premises = self.build_litex_to_lean_ir_supported_inferred_premises(
                    &verification.proof_scope.assumption_infers,
                )?;
                let context = LitexToLeanIrConstructionContext::default()
                    .with_infer_result(&verification.proof_scope.assumption_infers);
                let steps = verification
                    .proof_steps
                    .iter()
                    .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
                    .collect::<Result<Vec<_>, RuntimeError>>()?;
                let mut conclusions = Vec::with_capacity(verification.forall_fact.then_facts.len());
                for result in &verification.conclusion_checks {
                    if result.factual_success().is_none() {
                        return Err(litex_to_lean_ir_error(
                            &stmt.line_file,
                            "forall `example` verification did not retain a factual conclusion",
                        ));
                    }
                    conclusions.push(self.build_litex_to_lean_ir_fact_from_result(
                        result,
                        "example forall conclusion",
                        &context,
                    )?);
                }
                let target = LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Anonymous,
                    proposition,
                    proof: LitexToLeanFactProofIr::ForallIntroduction {
                        parameter_premises,
                        premises,
                        inferred_premises,
                        conclusions,
                    },
                };
                let block = LitexToLeanLocalProofBlockIr {
                    premise_aliases: Vec::new(),
                    assumption_inferred_facts: Vec::new(),
                    well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                        &WellDefinednessCertificate::default(),
                        &context,
                    )?,
                    steps,
                };
                (target, block, context)
            }
        };

        let source_well_definedness = match verification {
            SuccessVerifyClaimResult::Fact(verification) => &verification.well_definedness,
            SuccessVerifyClaimResult::Forall(verification) => &verification.well_definedness,
        };
        let recursive_well_definedness =
            crate::result::project_compositional_well_definedness(source_well_definedness)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let well_definedness = self.build_litex_to_lean_ir_well_definedness_certificate(
            &recursive_well_definedness,
            &context,
        )?;
        block.well_definedness = well_definedness.clone();

        Ok(LitexToLeanStatementIr::ProofBlock(
            LitexToLeanProofBlockStmtIr::ExampleStmt(LitexToLeanExampleStmtIr::new(
                stmt.line_file.clone(),
                target,
                block,
                well_definedness,
            )),
        ))
    }

    fn build_litex_to_lean_ir_sketch_statement(
        &self,
        stmt: &SketchStmt,
        success: &SuccessStmtCommonResult,
        proof: Option<&SuccessSketchProofResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        if !success.infers.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "a `sketch` unexpectedly exported facts to the surrounding environment",
            ));
        }
        let proof = proof.ok_or_else(|| {
            litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified `sketch` reached Litex-to-Lean without recursive proof evidence",
            )
        })?;
        let scope = &proof.proof_scope;
        if !scope.assumption_infers.is_empty() || !scope.assumption_components.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "a `sketch` retained unexpected assumptions in its local proof scope",
            ));
        }
        if proof.proof_steps.len() != stmt.proof.len() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "`sketch` proof-scope results do not match the source statement order",
            ));
        }
        let context = LitexToLeanIrConstructionContext::default();
        let steps = proof
            .proof_steps
            .iter()
            .map(|result| self.build_litex_to_lean_ir_nested_statement(result))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let block = LitexToLeanLocalProofBlockIr {
            premise_aliases: Vec::new(),
            assumption_inferred_facts: Vec::new(),
            well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                &WellDefinednessCertificate::default(),
                &context,
            )?,
            steps,
        };
        Ok(LitexToLeanStatementIr::ProofBlock(
            LitexToLeanProofBlockStmtIr::SketchStmt(LitexToLeanSketchStmtIr::new(
                stmt.line_file.clone(),
                block,
                self.build_litex_to_lean_ir_well_definedness_certificate(
                    &WellDefinednessCertificate::default(),
                    &context,
                )?,
            )),
        ))
    }

    fn build_litex_to_lean_ir_named_theorem_statement(
        &self,
        stmt: &DefThmStmt,
        success: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyTheoremResult>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let verification = verification.ok_or_else(|| {
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
        if verification.proof_steps.len() != stmt.prove_process.len()
            || verification.conclusion_checks.len() != verification.forall_fact.then_facts.len()
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
            .proof_scope
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
                .proof_scope
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
        let inferred_premises = self.build_litex_to_lean_ir_supported_inferred_premises(
            &verification.proof_scope.assumption_infers,
        )?;
        let theorem_context = LitexToLeanIrConstructionContext::default()
            .with_infer_result(&verification.proof_scope.assumption_infers);
        let recursive_well_definedness =
            crate::result::project_compositional_well_definedness(&verification.well_definedness)
                .map_err(|message| litex_to_lean_ir_error(&stmt.line_file, message))?;
        let theorem_well_definedness = self.build_litex_to_lean_ir_well_definedness_certificate(
            &recursive_well_definedness,
            &theorem_context,
        )?;
        let proof_steps = verification
            .proof_steps
            .iter()
            .map(|result| {
                Ok(LitexToLeanDefThmStmtProofStepIr {
                    statement: self.build_litex_to_lean_ir_nested_statement(result)?,
                })
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let mut conclusions = Vec::with_capacity(verification.forall_fact.then_facts.len());
        for result in &verification.conclusion_checks {
            conclusions.push(self.build_litex_to_lean_ir_fact_from_result(
                result,
                "theorem conclusion",
                &theorem_context,
            )?);
        }
        let theorem = LitexToLeanFactIr {
            storage: matching_outputs[0].fact_id.into(),
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
        if theorem.stored_fact_id().is_none() && stored_projections.is_empty() {
            return Err(litex_to_lean_ir_error(
                &stmt.line_file,
                "a verified theorem had neither a complete FactId nor stored projections",
            ));
        }

        Ok(LitexToLeanStatementIr::DefThmStmt(
            LitexToLeanDefThmStmtIr {
                name: verification.name.clone(),
                theorem,
                proof_steps,
                stored_projections,
                inferred_facts: self
                    .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
                well_definedness: theorem_well_definedness,
            },
        ))
    }

    fn build_litex_to_lean_ir_fact_from_success(
        &self,
        success: &SuccessFactStmtResult,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        let context = self.well_definedness_context_for_factual_success(success);
        self.build_litex_to_lean_ir_fact_from_success_with_context(success, &context)
    }

    fn build_litex_to_lean_ir_projected_forall_statement(
        &self,
        success: &SuccessFactStmtResult,
        source: LitexToLeanFactIr,
        mut excluded: HashSet<String>,
    ) -> Result<LitexToLeanStatementIr, RuntimeError> {
        let facts = self.build_litex_to_lean_ir_forall_projections(
            &success.infers,
            &source,
            &mut excluded,
        )?;
        let Fact::ForallFact(_) = &source.proposition else {
            return Err(litex_to_lean_ir_error(
                &source.proposition.line_file(),
                "a verified non-forall fact was not assigned a stored FactId",
            ));
        };
        // A fully verified reflexive forall may deliberately be omitted from
        // the runtime's stored environment because no later proof needs to
        // cite it. It is still a source statement and still carries complete
        // ForallIntroduction and WD evidence, so retain it in statement IR
        // with `fact_id = None`. Emitters may compile the theorem but cannot
        // invent a citation identity for later statements.

        let recursive_well_definedness =
            crate::result::project_compositional_well_definedness(&success.well_definedness)
                .map_err(|message| {
                    litex_to_lean_ir_error(&source.proposition.line_file(), message)
                })?;
        Ok(LitexToLeanStatementIr::Fact(LitexToLeanFactStatementIr {
            source,
            stored_projections: facts,
            inferred_facts: self
                .build_litex_to_lean_ir_inferred_facts(&success.infers, &excluded)?,
            well_definedness: self.build_litex_to_lean_ir_well_definedness_certificate(
                &recursive_well_definedness,
                &self.well_definedness_context_for_factual_success(success),
            )?,
        }))
    }

    fn build_litex_to_lean_ir_forall_projections(
        &self,
        infer_result: &SuccessInferResult,
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
                    storage: LitexToLeanFactStorageIr::Stored(fact_id),
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
        success: &SuccessFactStmtResult,
    ) -> LitexToLeanIrConstructionContext {
        match success.underlying_verified_by() {
            SuccessFactProofResult::ForallProof(result) => {
                let mut context = LitexToLeanIrConstructionContext::default()
                    .with_infer_result(&result.assumption_infers);
                let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(wd)) =
                    success.well_definedness.recursive.as_deref()
                else {
                    return context;
                };

                let proof_assumptions = result
                    .assumption_infers
                    .store_fact_outputs
                    .iter()
                    .filter_map(|output| {
                        output
                            .fact_id
                            .map(|fact_id| (&output.itself_and_why_itself_is_stored.0, fact_id))
                    })
                    .collect::<Vec<_>>();
                let wd_assumptions = wd
                    .binder
                    .parameter_groups
                    .iter()
                    .flat_map(|group| group.parameters.iter())
                    .filter_map(|parameter| {
                        parameter
                            .infers
                            .store_fact_outputs
                            .iter()
                            .find(|output| {
                                output.itself_and_why_itself_is_stored.0.to_string()
                                    == parameter.proposition.to_string()
                            })
                            .and_then(|output| output.fact_id)
                            .map(|fact_id| (&parameter.proposition, fact_id))
                    })
                    .chain(wd.premises.iter().filter_map(|premise| {
                        premise
                            .store
                            .fact_id
                            .map(|fact_id| (&premise.proposition, fact_id))
                    }))
                    .collect::<Vec<_>>();
                if wd_assumptions.len() == proof_assumptions.len() {
                    for ((wd_fact, wd_id), (proof_fact, proof_id)) in
                        wd_assumptions.iter().zip(proof_assumptions.iter())
                    {
                        if wd_fact.to_string() == proof_fact.to_string() {
                            context.fact_id_aliases.insert(*wd_id, *proof_id);
                        }
                    }
                }

                if wd.conclusions.len() == result.proves.len() {
                    for (wd_conclusion, proof_conclusion) in
                        wd.conclusions.iter().zip(result.proves.iter())
                    {
                        let Some(wd_id) = wd_conclusion.store.fact_id else {
                            continue;
                        };
                        let Some(proof_success) = proof_conclusion.result.factual_success() else {
                            continue;
                        };
                        let Some(proof_id) = proof_success.fact_id else {
                            continue;
                        };
                        if wd_conclusion.proposition.to_string() == proof_success.fact().to_string()
                        {
                            context.fact_id_aliases.insert(wd_id, proof_id);
                        }
                    }
                }
                context
            }
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
            let fact = self.build_litex_to_lean_ir_fact_from_verification_with_context(
                evidence.proof.as_ref(),
                None,
                context,
            )?;
            let proof_fact = evidence.proof.fact();
            if fact.proposition.to_string() != proof_fact.to_string() {
                return Err(litex_to_lean_ir_error(
                    &proof_fact.line_file(),
                    "well-definedness certificate proof changed its proposition during IR lowering",
                ));
            }
            facts.push(LitexToLeanWellDefinednessFactIr {
                well_defined_fact_id: evidence.well_defined_fact_id,
                fact,
                ambient_binder_scope_ids: evidence.ambient_binder_scope_ids.clone(),
            });
        }
        let facts_by_well_defined_id = facts
            .iter()
            .map(|evidence| (evidence.well_defined_fact_id, &evidence.fact.proposition))
            .collect::<HashMap<_, _>>();
        let mut objects = Vec::with_capacity(certificate.objects.len());
        let mut objects_by_id = HashMap::new();
        for evidence in certificate.objects.iter() {
            if objects_by_id
                .insert(evidence.well_defined_obj_id, evidence.object.clone())
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
                    })
                })
                .collect::<Result<Vec<_>, RuntimeError>>()?;
            objects.push(LitexToLeanWellDefinednessObjectIr {
                well_defined_obj_id: evidence.well_defined_obj_id,
                source_object: evidence.object.clone(),
                function_contracts: evidence.function_contracts.clone(),
                intrinsic_result_set,
                child_uses: evidence.child_uses.clone(),
                well_defined_fact_ids: evidence.well_defined_fact_ids.clone(),
                target_requirements,
                ambient_binder_scope_ids: evidence.ambient_binder_scope_ids.clone(),
                owned_binder_scope_id: evidence.owned_binder_scope_id,
            });
        }
        let mut binder_scopes = Vec::with_capacity(certificate.binder_scopes.len());
        for evidence in certificate.binder_scopes.iter() {
            let scope = &evidence.scope;
            let inferred_premises =
                self.build_litex_to_lean_ir_supported_inferred_premises(&scope.assumption_infers)?;
            binder_scopes.push(LitexToLeanWellDefinednessBinderScopeIr {
                scope_id: scope.id,
                owner_object: scope.owner_object.clone(),
                ambient_scope_ids: scope.ambient_scope_ids.clone(),
                premises: scope
                    .premises
                    .iter()
                    .map(|premise| LitexToLeanWellDefinednessBinderPremiseIr {
                        role: premise.role,
                        symbol_id: premise.symbol_id,
                        fact_id: premise.fact_id,
                        proposition: premise.proposition.clone(),
                    })
                    .collect(),
                inferred_premises,
            });
        }
        for root_use in certificate.root_proof_uses.iter() {
            if !objects_by_id.contains_key(&root_use.well_defined_obj_id) {
                return Err(litex_to_lean_ir_error(
                    &default_line_file(),
                    "well-definedness root use references a missing object proof",
                ));
            }
        }
        for source_use in certificate.source_object_uses.iter() {
            if !objects_by_id.contains_key(&source_use.well_defined_obj_id) {
                return Err(litex_to_lean_ir_error(
                    &default_line_file(),
                    "source-object WD use references a missing object proof",
                ));
            }
        }
        let mut target_requirements = Vec::with_capacity(certificate.target_requirements.len());
        for requirement in certificate.target_requirements.iter() {
            let Some(expected_fact) =
                facts_by_well_defined_id.get(&requirement.well_defined_fact_id)
            else {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement references a missing fact",
                ));
            };
            if expected_fact.to_string() != requirement.expected_proposition.to_string() {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement changed its verifier proposition",
                ));
            }
            let source_use = certificate
                .source_object_uses
                .iter()
                .find(|source_use| {
                    source_use.source_occurrence_id == requirement.source_occurrence_id
                })
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &requirement.expected_proposition.line_file(),
                        "target well-definedness requirement has no exact source-object use",
                    )
                })?;
            if source_use.phase != requirement.phase {
                return Err(litex_to_lean_ir_error(
                    &requirement.expected_proposition.line_file(),
                    "target well-definedness requirement changed its verifier execution phase",
                ));
            }
            let Some(source_object) = objects_by_id.get(&requirement.well_defined_obj_id) else {
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
                well_defined_obj_id: requirement.well_defined_obj_id,
                role: requirement.role,
                well_defined_fact_id: requirement.well_defined_fact_id,
            });
        }
        let ir = LitexToLeanWellDefinednessCertificateIr {
            root_proof_uses: certificate.root_proof_uses.clone(),
            source_object_uses: certificate.source_object_uses.clone(),
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
            binder_scopes,
        };
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(&ir)
            .map_err(|message| litex_to_lean_ir_error(&default_line_file(), message))?;
        Ok(ir)
    }

    fn build_litex_to_lean_ir_fact_from_success_with_context(
        &self,
        success: &SuccessFactStmtResult,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        self.build_litex_to_lean_ir_fact_from_verification_with_context(
            success.verification.as_ref(),
            success.fact_id,
            context,
        )
    }

    fn build_litex_to_lean_ir_fact_from_verification_with_context(
        &self,
        verification: &SuccessVerifyFactResult,
        fact_id: Option<FactId>,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        Ok(LitexToLeanFactIr {
            storage: fact_id.into(),
            proposition: verification.fact(),
            proof: self.build_litex_to_lean_ir_verified_by(
                &verification.fact(),
                fact_id,
                verification.proof(),
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
            return Err(litex_to_lean_ir_error(
                &result.line_file(),
                format!("{} did not return a factual success", result_context),
            ));
        };
        self.build_litex_to_lean_ir_fact_from_success_with_context(success, context)
    }

    fn build_litex_to_lean_ir_checked_function_definition_reduction(
        &self,
        goal: &Fact,
        reduction: &CheckedFunctionDefinitionReductionEvidence,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(goal_equality)) = goal else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition reduction was attached to a non-equality goal",
            ));
        };
        let (expected_application, expected_other) = if reduction.application_is_left {
            (&goal_equality.left, &goal_equality.right)
        } else {
            (&goal_equality.right, &goal_equality.left)
        };
        if obj_equality_key(expected_application) != obj_equality_key(&reduction.application_side)
            || obj_equality_key(expected_other) != obj_equality_key(&reduction.other_side)
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition reduction does not match the recorded goal orientation",
            ));
        }
        if obj_equality_key(&goal_equality.left) == obj_equality_key(&goal_equality.right) {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ObjectReflexivity,
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        if !reduction.reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(
                &reduction.reduced,
                &reduction.other_side,
            )
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "the Litex-to-Lean function-definition reduction adapter requires an alpha-equivalent reduced result",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) =
            &reduction.defining_equality
        else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition reduction source is not a defining equality",
            ));
        };
        if obj_equality_key(&defining_equality.left)
            != obj_equality_key(&reduction.definition_object)
            || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
        {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition reduction source does not define the recorded function object",
            ));
        }
        let definition = LitexToLeanObjectIr::lower(&reduction.definition_object)
            .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
        if !matches!(definition, LitexToLeanObjectIr::Symbol { .. }) {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "checked function-definition reduction currently requires a named function symbol",
            ));
        }
        for object in [
            &reduction.application_side,
            &reduction.reduced,
            &reduction.other_side,
        ] {
            LitexToLeanObjectIr::lower(object)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
        }
        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::CheckedFunctionDefinitionReduction {
                defining_equality_fact_id: reduction.defining_equality_fact_id,
                application_side: if reduction.application_is_left {
                    LitexToLeanEqualitySideIr::Left
                } else {
                    LitexToLeanEqualitySideIr::Right
                },
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
            requirement.make_anonymous();
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
            premise.make_anonymous();
            premises.push(premise);
        }

        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::DefinitionReduction,
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
        let instantiated_types = self.instantiator.inst_param_def_with_type_one_by_one(
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
                self.instantiator.inst_fact(
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
        verified_by: &SuccessFactProofResult,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result) => self
                .build_litex_to_lean_ir_builtin_rule_application(
                    goal,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                ),
            SuccessFactProofResult::BuiltinStrategy(result) => self
                .build_litex_to_lean_ir_builtin_strategy_application(
                    goal,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                ),
            SuccessFactProofResult::Fact(result) => {
                if let Some(reduction) = result.checked_function_definition_reduction.as_ref() {
                    return self.build_litex_to_lean_ir_checked_function_definition_reduction(
                        goal, reduction,
                    );
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
                        &evidence.argument_verification.checks,
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
                        Err(litex_to_lean_ir_error(
                            &goal.line_file(),
                            "concrete prop citation has no retained parameter and clause checks",
                        ))
                    }
                    Stmt::DefStrategyStmt(strategy) => Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        format!(
                            "strategy `{}` reached IR capture without recursively retained rule/fact evidence",
                            strategy.name
                        ),
                    )),
                    cited => Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        format!(
                            "citation kind `{}` is not represented by the Litex-to-Lean MVP",
                            cited.stmt_type_name()
                        ),
                    )),
                }
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.build_litex_to_lean_ir_known_forall(goal, result, context)
            }
            SuccessFactProofResult::CombinedProofs(result) => {
                let mut steps = Vec::with_capacity(result.cite_what.len());
                for step in result.cite_what.iter() {
                    steps.push(self.build_litex_to_lean_ir_verified_bys_step(
                        step,
                        goal,
                        goal_fact_id,
                        context,
                    )?);
                }
                let conjunction_components = match goal {
                    Fact::AndFact(and_fact) => Some(
                        and_fact
                            .facts
                            .iter()
                            .cloned()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                    ),
                    Fact::ChainFact(chain_fact) => Some(
                        chain_fact
                            .facts()?
                            .into_iter()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                    ),
                    _ => None,
                };
                if let Some(components) = conjunction_components {
                    if components.len() == steps.len()
                        && components
                            .iter()
                            .zip(steps.iter())
                            .all(|(expected, actual)| {
                                expected.to_string() == actual.proposition.to_string()
                            })
                    {
                        return Ok(LitexToLeanFactProofIr::RuleApplication {
                            rule: LitexToLeanProofRuleIr::AndIntroduction,
                            parameter_requirements: Vec::new(),
                            premises: steps,
                        });
                    }
                }
                Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "composite proof does not align with the target's ordered conjunction components",
                ))
            }
            SuccessFactProofResult::ForallProof(result) => {
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
                let mut inferred_premises = self
                    .build_litex_to_lean_ir_supported_inferred_premises(
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
                add_cited_conjunction_projections(&premises, &conclusions, &mut inferred_premises)?;
                Ok(LitexToLeanFactProofIr::ForallIntroduction {
                    parameter_premises,
                    premises,
                    inferred_premises,
                    conclusions,
                })
            }
            SuccessFactProofResult::Transform(_) => Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "Litex-to-Lean does not yet lower recursive fact transformation results",
            )),
            SuccessFactProofResult::Reuse(result) => self.build_litex_to_lean_ir_verified_by(
                goal,
                goal_fact_id,
                result.source.proof(),
                context,
            ),
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
            Some(fact_id) => Some(
                context
                    .fact_id_aliases
                    .get(&fact_id)
                    .copied()
                    .unwrap_or(fact_id),
            ),
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
                rule: LitexToLeanProofRuleIr::ComparisonNotationDuality,
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        let Some(source_fact_id) = source_fact_id else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!("verified citation `{}` has no stored FactId", source_fact),
            ));
        };
        // Preserve the existing closed-membership certificate even when the
        // verifier also records how a differently spelled citation resolved
        // to this closed goal. The checked target rule is dependency-free and
        // more precise than replaying an incidental citation route.
        if source_fact.to_string() != goal.to_string()
            && crate::litex_to_lean_ir::is_closed_real_membership(goal)
        {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedStandardMembership,
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
                    rule: LitexToLeanProofRuleIr::ComparisonNotationDuality,
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
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
                    && Runtime::exist_fact_normalized_body_string(&self.instantiator, source_exist)?
                        == Runtime::exist_fact_normalized_body_string(
                            &self.instantiator,
                            goal_exist,
                        )?
                {
                    return Ok(LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                        source_fact_id,
                    });
                }
            }
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "citation `{}` changed goal `{}` without structured rewrite evidence",
                    source_fact, goal
                ),
            ));
        }

        let mut current = LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
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
            )?;
        } else if current.proposition.to_string() != citation_target.to_string() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "citation `{}` does not prove transformation source `{}`",
                    source_fact, citation_target
                ),
            ));
        }

        if let Some(transformation) = fact_transformation {
            current = self.build_litex_to_lean_ir_fact_transformation(current, transformation)?;
        }

        if current.proposition.to_string() != goal.to_string() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "fact transformations ended at `{}` instead of goal `{}`",
                    current.proposition, goal
                ),
            ));
        }
        Ok(current.proof)
    }

    fn build_litex_to_lean_ir_equality_rewrite_fact(
        &self,
        result: &Fact,
        source: LitexToLeanFactIr,
        equality_transport: &EqualityTransportEvidence,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        if equality_transport.steps.is_empty() {
            if source.proposition.to_string() == result.to_string() {
                return Ok(source);
            }
            return Err(litex_to_lean_ir_error(
                &result.line_file(),
                format!(
                    "empty equality transport changed `{}` to `{}`",
                    source.proposition, result
                ),
            ));
        }

        let mut premises = Vec::with_capacity(equality_transport.steps.len() + 1);
        premises.push(source);
        for rewrite in equality_transport.steps.iter() {
            let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
            let Some(equality_fact_id) = rewrite.equality_fact_id else {
                return Err(litex_to_lean_ir_error(
                    &result.line_file(),
                    format!(
                            "equality transport `{}` -> `{}` through `{}` has no compiler proof provenance",
                            rewrite.from, rewrite.to, equality_fact
                    ),
                ));
            };
            let left_key = obj_equality_key(&rewrite.equality.left);
            let right_key = obj_equality_key(&rewrite.equality.right);
            let from_key = obj_equality_key(&rewrite.from);
            let to_key = obj_equality_key(&rewrite.to);
            if !((from_key == left_key && to_key == right_key)
                || (from_key == right_key && to_key == left_key))
            {
                return Err(litex_to_lean_ir_error(
                    &result.line_file(),
                    format!(
                        "equality rewrite edge `{}` -> `{}` is not oriented by `{}`",
                        rewrite.from, rewrite.to, equality_fact
                    ),
                ));
            }
            premises.push(LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Stored(equality_fact_id),
                proposition: equality_fact,
                proof: LitexToLeanFactProofIr::KnownFactCitation {
                    source_fact_id: equality_fact_id,
                },
            });
        }

        Ok(LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Anonymous,
            proposition: result.clone(),
            proof: LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::EqualityRewrite,
                parameter_requirements: Vec::new(),
                premises,
            },
        })
    }

    fn build_litex_to_lean_ir_fact_transformation(
        &self,
        mut current: LitexToLeanFactIr,
        transformation: &FactTransformationEvidence,
    ) -> Result<LitexToLeanFactIr, RuntimeError> {
        if current.proposition.to_string() != transformation.source.to_string() {
            return Err(litex_to_lean_ir_error(
                &transformation.source.line_file(),
                format!(
                    "fact transformation source `{}` does not match proved premise `{}`",
                    transformation.source, current.proposition
                ),
            ));
        }
        for step in transformation.steps.iter() {
            current = match &step.rule {
                FactTransformationRule::RationalNormalization => {
                    if !facts_align_by_rational_normalization(&current.proposition, &step.result) {
                        return Err(litex_to_lean_ir_error(
                            &step.result.line_file(),
                            format!(
                                "normalization source `{}` does not align with result `{}`",
                                current.proposition, step.result
                            ),
                        ));
                    }
                    LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Anonymous,
                        proposition: step.result.clone(),
                        proof: LitexToLeanFactProofIr::RuleApplication {
                            rule: LitexToLeanProofRuleIr::RationalNormalization,
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
                    )?,
            };
        }
        Ok(current)
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
        // A forall conclusion can cite one of its temporary premises. The
        // local environment has already been popped when the completed result
        // list is lowered. Prefer the verifier-retained goal identity before
        // consulting the final ambient runtime, which may now contain a later
        // statement with the same proposition.
        if cited_fact.to_string() == goal.to_string() {
            return Ok(goal_fact_id);
        }
        Ok(None)
    }

    fn build_litex_to_lean_ir_known_forall(
        &self,
        goal: &Fact,
        result: &SuccessInstantiateKnownForallResult,
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let Stmt::Fact(source_fact) = result.cite_what.as_ref() else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-forall verification did not cite a fact",
            ));
        };
        let Fact::ForallFact(source_forall) = source_fact else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "known-forall verification cited a non-forall fact",
            ));
        };
        let source_fact_id = match result.source_fact_id {
            Some(fact_id) => Some(fact_id),
            None => self.citation_fact_id(source_fact, source_fact, None, context)?,
        };
        let Some(source_fact_id) = source_fact_id else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!("known forall `{}` has no stored FactId", source_fact),
            ));
        };

        let mut source_parameters = Vec::new();
        for group in source_forall.params_def_with_type.groups.iter() {
            if group.params.is_empty() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "known forall contains an empty parameter group",
                ));
            }
            let param_type = build_litex_to_lean_ir_parameter_type(&group.param_type)?;
            for parameter in group.params.iter() {
                source_parameters.push((parameter.name().to_string(), param_type.clone()));
            }
        }
        if result.instantiation.len() != source_parameters.len() {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "known forall `{}` recorded {} arguments for {} parameter types",
                    source_fact,
                    result.instantiation.len(),
                    source_parameters.len()
                ),
            ));
        }
        let arguments = result
            .instantiation
            .iter()
            .zip(source_parameters.iter())
            .map(|(item, (parameter, _))| {
                if item.param != *parameter {
                    return Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        "known forall changed its retained parameter order",
                    ));
                }
                Ok(item.arg_obj.clone())
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
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
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "known forall `{}` recorded {} arguments but {} parameter requirements",
                    source_fact,
                    arguments.len(),
                    parameter_requirements.len()
                ),
            ));
        }

        let Some(source_conclusion) = source_forall.then_facts.first() else {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!("known forall `{}` has no conclusion", source_fact),
            ));
        };
        if source_forall.then_facts.len() != 1 {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                format!(
                    "known forall `{}` has {} conclusions instead of one matched conclusion",
                    source_fact,
                    source_forall.then_facts.len()
                ),
            ));
        }
        let argument_objects = arguments.clone();
        let param_to_arg_map = source_forall
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&argument_objects);
        let instantiated_conclusion = self.instantiator.inst_fact(
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
            storage: LitexToLeanFactStorageIr::Anonymous,
            proposition: instantiated_conclusion.clone(),
            proof: application,
        };
        if facts_align_by_rational_normalization(&instantiated_conclusion, goal) {
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::RationalNormalization,
                parameter_requirements: Vec::new(),
                premises: vec![instantiated_fact],
            });
        }

        Err(litex_to_lean_ir_error(
            &goal.line_file(),
            format!(
                "known-forall instance `{}` does not structurally match goal `{}`",
                instantiated_conclusion, goal
            ),
        ))
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
        if let Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) = evidence {
            let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = goal else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "object-reflexivity evidence targets a non-equality fact",
                ));
            };
            if evidence.expected_target.to_string() != goal.to_string()
                || !subgoals.is_empty()
                || obj_equality_key(&equality.left) != obj_equality_key(&equality.right)
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "object-reflexivity evidence changed its target or children",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ObjectReflexivity,
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        if let Some(BuiltinRuleEvidence::RationalNormalization(evidence)) = evidence {
            let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = goal else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "rational-normalization evidence targets a non-equality fact",
                ));
            };
            let left = equality
                .left
                .evaluate_to_normalized_decimal_number()
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &goal.line_file(),
                        "rational-normalization left side no longer evaluates",
                    )
                })?;
            let right = equality
                .right
                .evaluate_to_normalized_decimal_number()
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &goal.line_file(),
                        "rational-normalization right side no longer evaluates",
                    )
                })?;
            if evidence.expected_target.to_string() != goal.to_string()
                || !subgoals.is_empty()
                || obj_equality_key(&equality.left)
                    != obj_equality_key(&evidence.left_evaluation.expression)
                || obj_equality_key(&equality.right)
                    != obj_equality_key(&evidence.right_evaluation.expression)
                || left.normalized_value != evidence.left_evaluation.value.normalized_value
                || right.normalized_value != evidence.right_evaluation.value.normalized_value
                || left.normalized_value != right.normalized_value
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "rational-normalization evidence changed its target or normal forms",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::RationalNormalization,
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
        if let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = evidence {
            let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = goal else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "standard-set nonempty evidence targets another fact family",
                ));
            };
            if evidence.expected_target.to_string() != goal.to_string()
                || !subgoals.is_empty()
                || !matches!(
                    &nonempty.set,
                    Obj::StandardSet(target_set) if *target_set == evidence.target_set
                )
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "standard-set nonempty evidence changed its target or children",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::StandardSetNonempty,
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
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
            LitexToLeanObjectIr::lower(&evidence.typed_return_set)
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
                rule: LitexToLeanProofRuleIr::FunctionApplicationReturnMembership,
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "disjunction-introduction evidence was retargeted after verification",
                ));
            }
            let Fact::OrFact(disjunction) = &evidence.expected_target else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "disjunction-introduction evidence retained a non-disjunction target",
                ));
            };
            let Some(selected) = disjunction.facts.get(evidence.selected_index) else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "disjunction-introduction evidence selected an out-of-range branch",
                ));
            };
            let selected: Fact = selected.clone().into();
            if selected.to_string() != evidence.expected_selected.to_string() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "disjunction-introduction evidence changed its selected branch",
                ));
            }
            let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
            if premises.len() != 1
                || premises[0].proposition.to_string() != evidence.expected_selected.to_string()
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "disjunction-introduction evidence lost its exact selected proof",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DisjunctionIntroduction {
                    selected_index: evidence.selected_index,
                },
                parameter_requirements: Vec::new(),
                premises,
            });
        }
        if let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = evidence {
            if evidence.expected_target.to_string() != goal.to_string() || !subgoals.is_empty() {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "closed numeric membership evidence changed its target or gained premises",
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = goal else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "closed numeric membership evidence targets a non-membership fact",
                ));
            };
            if membership.element.to_string() != evidence.evaluation.expression.to_string()
                || !matches!(
                    &membership.set,
                    Obj::StandardSet(target_set) if *target_set == evidence.target_set
                )
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "closed numeric membership evidence changed its expression or target set",
                ));
            }
            let reevaluated = evidence
                .evaluation
                .expression
                .evaluate_to_normalized_decimal_number()
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &goal.line_file(),
                        "closed numeric membership evidence no longer evaluates",
                    )
                })?;
            if reevaluated.normalized_value != evidence.evaluation.value.normalized_value {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "closed numeric membership evidence changed its normalized value",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedNumericMembership(Box::new(
                    LitexToLeanClosedNumericMembershipProofIr {
                        target_set: evidence.target_set,
                        evaluation: evidence.evaluation.clone(),
                    },
                )),
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
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
                rule: LitexToLeanProofRuleIr::ClosedNumericComparison,
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
            let base_set = match target_set {
                StandardSet::ZStar => StandardSet::Z,
                StandardSet::QStar => StandardSet::Q,
                StandardSet::RStar => StandardSet::R,
                StandardSet::CStar => StandardSet::C,
                _ => {
                    return Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        "refined numeric membership has no Lean replay adapter",
                    ))
                }
            };
            let [base_premise, nonzero_premise] = premises.as_slice() else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "nonzero numeric membership did not retain exactly two premises",
                ));
            };
            let Fact::AtomicFact(AtomicFact::InFact(base_membership)) = &base_premise.proposition
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "nonzero numeric membership lost its base-carrier premise",
                ));
            };
            let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = &nonzero_premise.proposition
            else {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "nonzero numeric membership lost its non-equality premise",
                ));
            };
            if obj_equality_key(&base_membership.element)
                != obj_equality_key(&expected_target.element)
                || !matches!(&base_membership.set, Obj::StandardSet(actual) if *actual == base_set)
                || obj_equality_key(&nonzero.left) != obj_equality_key(&expected_target.element)
                || !matches!(&nonzero.right, Obj::Number(number) if number.normalized_value == "0")
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "nonzero numeric membership changed its base carrier, element, or zero orientation",
                ));
            }
            return Ok(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::NonzeroNumericMembership,
                ),
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
            LitexToLeanObjectIr::lower(&target.element)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let function_set = LitexToLeanObjectIr::lower(&target.set)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            if !matches!(function_set, LitexToLeanObjectIr::FunctionSet { .. }) {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "function-set membership evidence lowered to a non-function-space object",
                ));
            }
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "function-set membership has no Lean replay adapter",
            ));
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
                rule: LitexToLeanProofRuleIr::SetBuilderMembership,
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
                LitexToLeanBuiltinRuleIr::try_from_builtin_rule_evidence(evidence).ok_or_else(
                    || {
                        litex_to_lean_ir_error(
                            &goal.line_file(),
                            format!(
                                "builtin evidence `{evidence:?}` has no Litex-to-Lean IR representation"
                            ),
                        )
                    },
                )?,
            ),
            None if label == "calculation"
                && matches!(
                    goal,
                    Fact::AtomicFact(AtomicFact::EqualFact(equality))
                        if equality
                            .left
                            .two_objs_can_be_calculated_and_equal_by_calculation(
                                &equality.right,
                            )
                ) =>
            {
                LitexToLeanProofRuleIr::RationalNormalization
            }
            None => LitexToLeanProofRuleIr::try_from_verified_builtin_label(label, goal)
                .ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &goal.line_file(),
                        format!(
                            "verified builtin `{label}` has no supported Litex-to-Lean proof rule",
                        ),
                    )
                })?,
        };
        let premises = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
        Ok(LitexToLeanFactProofIr::RuleApplication {
            rule,
            parameter_requirements: Vec::new(),
            premises,
        })
    }

    fn build_litex_to_lean_ir_builtin_strategy_application(
        &self,
        goal: &Fact,
        label: &str,
        evidence: Option<&BuiltinRuleEvidence>,
        subgoals: &[StmtResult],
        context: &LitexToLeanIrConstructionContext,
    ) -> Result<LitexToLeanFactProofIr, RuntimeError> {
        let proof =
            if label == "additive sign strategy: normalized order goal" && evidence.is_none() {
                let [subgoal] = subgoals else {
                    return Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        "normalized additive strategy must retain exactly one subgoal",
                    ));
                };
                let normalized = self.build_litex_to_lean_ir_fact_from_result(
                    subgoal,
                    "normalized additive strategy subgoal",
                    context,
                )?;
                if !crate::litex_to_lean_ir::facts_are_comparison_notation_duals(
                    &normalized.proposition,
                    goal,
                ) {
                    return Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        "normalized additive strategy changed its order relation or operands",
                    ));
                }
                LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ComparisonNotationDuality,
                    parameter_requirements: Vec::new(),
                    premises: vec![normalized],
                }
            } else {
                self.build_litex_to_lean_ir_builtin_rule_application(
                    goal, label, evidence, subgoals, context,
                )?
            };
        Ok(LitexToLeanFactProofIr::UseBuiltinStrategy {
            proof: Box::new(proof),
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
            if !((from_key == left_key && to_key == right_key)
                || (from_key == right_key && to_key == left_key))
            {
                return Err(litex_to_lean_ir_error(
                    &goal.line_file(),
                    "known-equality evidence contains an edge with invalid orientation",
                ));
            }

            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            if let Some(available_fact_id) = context
                .local_fact_ids
                .get(&equality_fact.to_string())
                .copied()
            {
                if available_fact_id != step.source_fact_id {
                    return Err(litex_to_lean_ir_error(
                        &goal.line_file(),
                        format!(
                            "known-equality edge `{equality_fact}` cites a mismatched FactId {}",
                            step.source_fact_id.value()
                        ),
                    ));
                }
            }
            premises.push(LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Stored(step.source_fact_id),
                proposition: equality_fact,
                proof: LitexToLeanFactProofIr::KnownFactCitation {
                    source_fact_id: step.source_fact_id,
                },
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
            rule: LitexToLeanProofRuleIr::KnownEqualityPath,
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

        let reconstructed = self.instantiator.instantiate_existential_prop_definition(
            &evidence.fact,
            &evidence.definition,
            &goal.line_file(),
        )?;
        if !reconstructed.is_plain_exist()
            || Runtime::exist_fact_normalized_body_string(&self.instantiator, &reconstructed)?
                != Runtime::exist_fact_normalized_body_string(&self.instantiator, goal_existential)?
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
            rule: LitexToLeanProofRuleIr::DefinitionProjection,
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
        let expected_child_count =
            rule.schema().parameter_requirements.len() + rule.schema().premises.len();
        if subgoals.len() != expected_child_count {
            return Err(litex_to_lean_ir_error(
                &goal.line_file(),
                "local builtin certificate has the wrong child-proof arity",
            ));
        }
        let children = self.build_litex_to_lean_ir_subgoals(subgoals, context)?;
        let (requirement_children, premise_children) =
            children.split_at(rule.schema().parameter_requirements.len());
        for (template, child) in rule
            .schema()
            .parameter_requirements
            .iter()
            .zip(requirement_children)
        {
            let expected = self.instantiator.inst_atomic_fact(
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

        for (template, child) in rule.schema().premises.iter().zip(premise_children) {
            let expected = self.instantiator.inst_quantifier_free_fact(
                template,
                &param_to_arg_map,
                ParamObjType::Forall,
                Some(&goal.line_file()),
            )?;
            let actual = match &child.proposition {
                Fact::AtomicFact(fact) => QuantifierFreeFact::AtomicFact(fact.clone()),
                Fact::AndFact(fact) => QuantifierFreeFact::AndFact(fact.clone()),
                Fact::ChainFact(fact) => QuantifierFreeFact::ChainFact(fact.clone()),
                Fact::OrFact(fact) => QuantifierFreeFact::OrFact(fact.clone()),
                Fact::ExistFact(_)
                | Fact::ForallFact(_)
                | Fact::ForallFactWithIff(_)
                | Fact::NotForall(_) => {
                    return Err(litex_to_lean_ir_error(
                        &child.proposition.line_file(),
                        "local builtin premise child proof is not quantifier-free",
                    ));
                }
            };
            if !canonical_quantifier_free_facts_equal(&expected, &actual, MatchLimits::default())
                .map_err(|error| {
                    litex_to_lean_ir_error(&child.proposition.line_file(), error.message)
                })?
            {
                return Err(litex_to_lean_ir_error(
                    &child.proposition.line_file(),
                    "local builtin premise proof does not match its instantiated schema fact",
                ));
            }
        }

        let mut bindings = Vec::with_capacity(evidence.bindings.len());
        for (variable, object) in rule.schema().variables.iter().zip(&evidence.bindings) {
            let object = LitexToLeanObjectIr::lower(object)
                .map_err(|message| litex_to_lean_ir_error(&goal.line_file(), message))?;
            let instantiated_param_type = self.instantiator.inst_param_type(
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
        step: &SuccessCombinedFactProofItemResult,
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
            SuccessCombinedFactProofItemResult::ByBuiltinRule(result) => Ok(LitexToLeanFactIr {
                storage: step_fact_id(&result.verify_what)?.into(),
                proposition: result.verify_what.clone(),
                proof: self.build_litex_to_lean_ir_builtin_rule_application(
                    &result.verify_what,
                    &result.msg,
                    result.evidence.as_ref(),
                    &result.subgoals,
                    context,
                )?,
            }),
            SuccessCombinedFactProofItemResult::ByBuiltinStrategy(result) => {
                Ok(LitexToLeanFactIr {
                    storage: step_fact_id(&result.verify_what)?.into(),
                    proposition: result.verify_what.clone(),
                    proof: self.build_litex_to_lean_ir_builtin_strategy_application(
                        &result.verify_what,
                        &result.msg,
                        result.evidence.as_ref(),
                        &result.subgoals,
                        context,
                    )?,
                })
            }
            SuccessCombinedFactProofItemResult::ByFact(result) => {
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
                        &evidence.argument_verification.checks,
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
                            return Err(litex_to_lean_ir_error(
                            &result.verify_what.line_file(),
                            "concrete prop citation has no retained parameter and clause checks",
                        ));
                        }
                        cited => {
                            return Err(litex_to_lean_ir_error(
                                &result.verify_what.line_file(),
                                format!("unsupported composite citation `{}`", cited),
                            ));
                        }
                    }
                };
                Ok(LitexToLeanFactIr {
                    storage: step_fact_id(&result.verify_what)?.into(),
                    proposition: result.verify_what.clone(),
                    proof,
                })
            }
            SuccessCombinedFactProofItemResult::ByKnownForall(result) => Ok(LitexToLeanFactIr {
                storage: step_fact_id(&result.verify_what)?.into(),
                proposition: result.verify_what.clone(),
                proof: self.build_litex_to_lean_ir_known_forall(
                    &result.verify_what,
                    &result.result,
                    context,
                )?,
            }),
            SuccessCombinedFactProofItemResult::Reuse(result) => Ok(LitexToLeanFactIr {
                storage: step_fact_id(&result.statement)?.into(),
                proposition: result.statement.clone(),
                proof: self.build_litex_to_lean_ir_verified_by(
                    &result.statement,
                    step_fact_id(&result.statement)?,
                    result.source.proof(),
                    context,
                )?,
            }),
        }
    }

    fn build_litex_to_lean_ir_inferred_facts(
        &self,
        infer_result: &SuccessInferResult,
        excluded: &HashSet<String>,
    ) -> Result<Vec<LitexToLeanFactIr>, RuntimeError> {
        let mut seen = excluded.clone();
        let mut inferred = Vec::new();
        for output in infer_result.store_fact_outputs.iter() {
            let source_fact = &output.itself_and_why_itself_is_stored.0;
            let source_id = output.fact_id;
            let source_key = source_fact.to_string();
            if seen.insert(source_key) {
                if let Some(source_id) = source_id {
                    return Err(litex_to_lean_ir_error(
                        &source_fact.line_file(),
                        format!(
                            "environment FactId {} for `{}` has no checked Litex-to-Lean proof adapter",
                            source_id.value(),
                            source_fact
                        ),
                    ));
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
                let fact_id = *recorded_fact_id;
                let proof = build_litex_to_lean_ir_inferred_fact_proof(
                    self,
                    infer_result,
                    source_fact,
                    source_id,
                    fact,
                    fact_id,
                    &output.itself_and_why_itself_is_stored.1,
                )?;
                let Some(proof) = proof else {
                    if let Some(fact_id) = fact_id {
                        return Err(litex_to_lean_ir_error(
                            &fact.line_file(),
                            format!(
                                "environment FactId {} for inferred fact `{}` has no checked Litex-to-Lean proof adapter",
                                fact_id.value(),
                                fact
                            ),
                        ));
                    }
                    continue;
                };
                inferred.push(LitexToLeanFactIr {
                    storage: fact_id.into(),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }

    fn build_litex_to_lean_ir_supported_inferred_premises(
        &self,
        infer_result: &SuccessInferResult,
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
                let inferred_fact_id = *fact_id;
                let proof = build_litex_to_lean_ir_inferred_fact_proof(
                    self,
                    infer_result,
                    source_fact,
                    Some(source_fact_id),
                    fact,
                    inferred_fact_id,
                    &output.itself_and_why_itself_is_stored.1,
                )?;
                let Some(proof) = proof else {
                    continue;
                };
                let fact_id = (*fact_id).ok_or_else(|| {
                    litex_to_lean_ir_error(
                        &fact.line_file(),
                        "a supported forall inference reached Litex-to-Lean without a FactId",
                    )
                })?;
                inferred.push(LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Stored(fact_id),
                    proposition: fact.clone(),
                    proof,
                });
            }
        }
        Ok(inferred)
    }
}

fn add_cited_conjunction_projections(
    premises: &[LitexToLeanLocalPremiseIr],
    conclusions: &[LitexToLeanFactIr],
    inferred_premises: &mut Vec<LitexToLeanFactIr>,
) -> Result<(), RuntimeError> {
    for conclusion in conclusions {
        let Some(projected_fact_id) = known_fact_citation_id(&conclusion.proof) else {
            continue;
        };
        if inferred_premises
            .iter()
            .any(|inferred| inferred.stored_fact_id() == Some(projected_fact_id))
            || premises
                .iter()
                .any(|premise| premise.fact_id == projected_fact_id)
        {
            continue;
        }
        for premise in premises {
            let components = match &premise.fact {
                Fact::AndFact(and_fact) => and_fact
                    .facts
                    .iter()
                    .cloned()
                    .map(Fact::from)
                    .collect::<Vec<_>>(),
                Fact::ChainFact(chain_fact) => chain_fact
                    .facts()?
                    .into_iter()
                    .map(Fact::from)
                    .collect::<Vec<_>>(),
                _ => continue,
            };
            let Some(index) = components
                .iter()
                .position(|component| component.to_string() == conclusion.proposition.to_string())
            else {
                continue;
            };
            inferred_premises.push(LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Stored(projected_fact_id),
                proposition: conclusion.proposition.clone(),
                proof: LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ConjunctionProjection { index },
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(premise.fact_id),
                        proposition: premise.fact.clone(),
                        proof: LitexToLeanFactProofIr::KnownFactCitation {
                            source_fact_id: premise.fact_id,
                        },
                    }],
                },
            });
            break;
        }
    }
    Ok(())
}

fn known_fact_citation_id(proof: &LitexToLeanFactProofIr) -> Option<FactId> {
    match proof {
        LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => Some(*source_fact_id),
        LitexToLeanFactProofIr::UseBuiltinStrategy { proof } => known_fact_citation_id(proof),
        _ => None,
    }
}

fn build_litex_to_lean_ir_inferred_fact_proof(
    compiler: &LitexToLeanIrBuilder,
    infer_result: &SuccessInferResult,
    source_fact: &Fact,
    source_fact_id: Option<FactId>,
    inferred_fact: &Fact,
    inferred_fact_id: Option<FactId>,
    _reason: &str,
) -> Result<Option<LitexToLeanFactProofIr>, RuntimeError> {
    if let Some(proof) = build_typed_infer_rule_proof(
        infer_result,
        source_fact,
        source_fact_id,
        inferred_fact,
        inferred_fact_id,
    )? {
        return Ok(Some(proof));
    }
    if let (Fact::AtomicFact(AtomicFact::InFact(source)), Some(source_fact_id)) =
        (source_fact, source_fact_id)
    {
        if let Obj::ListSet(list_set) = &source.set {
            if list_set_membership_inference_matches(source, list_set, inferred_fact) {
                return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::Builtin(
                        LitexToLeanBuiltinRuleIr::ListSetMembershipElimination,
                    ),
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                        proposition: source_fact.clone(),
                        proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                    }],
                });
            }
        }
    }
    build_non_list_set_inferred_fact_proof(
        compiler,
        source_fact,
        source_fact_id,
        inferred_fact,
        _reason,
    )
}

fn build_typed_infer_rule_proof(
    infer_result: &SuccessInferResult,
    source_fact: &Fact,
    source_fact_id: Option<FactId>,
    inferred_fact: &Fact,
    inferred_fact_id: Option<FactId>,
) -> Result<Option<LitexToLeanFactProofIr>, RuntimeError> {
    let Some(inferred_fact_id) = inferred_fact_id else {
        return Ok(None);
    };
    let mut matches = infer_result.rule_applications.iter().filter(|application| {
        application
            .conclusions
            .iter()
            .any(|conclusion| conclusion.fact_id == Some(inferred_fact_id))
    });
    let Some(application) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        return Err(litex_to_lean_ir_error(
            &inferred_fact.line_file(),
            format!(
                "inferred FactId {} has more than one retained inference rule application",
                inferred_fact_id.value()
            ),
        ));
    }
    if application.premises.len() != 1 || application.conclusions.len() != 1 {
        return Err(litex_to_lean_ir_error(
            &inferred_fact.line_file(),
            "natural-membership inference changed its one-premise/one-conclusion contract",
        ));
    }
    let premise = &application.premises[0];
    let conclusion = &application.conclusions[0];
    let source_fact_id = source_fact_id.ok_or_else(|| {
        litex_to_lean_ir_error(
            &source_fact.line_file(),
            "typed inference source fact reached Litex-to-Lean without a FactId",
        )
    })?;
    if premise.fact_id != Some(source_fact_id)
        || premise.fact.to_string() != source_fact.to_string()
    {
        return Err(litex_to_lean_ir_error(
            &inferred_fact.line_file(),
            "typed inference premise does not cite the retained source fact and FactId",
        ));
    }
    if conclusion.fact_id != Some(inferred_fact_id)
        || conclusion.fact.to_string() != inferred_fact.to_string()
    {
        return Err(litex_to_lean_ir_error(
            &inferred_fact.line_file(),
            "typed inference conclusion does not match the retained inferred fact and FactId",
        ));
    }
    let rule = match application.rule {
        InferRule::NaturalMembershipImpliesNonnegative => {
            LitexToLeanBuiltinRuleIr::NaturalMembershipImpliesNonnegative
        }
    };
    Ok(Some(LitexToLeanFactProofIr::RuleApplication {
        rule: LitexToLeanProofRuleIr::Builtin(rule),
        parameter_requirements: Vec::new(),
        premises: vec![LitexToLeanFactIr {
            storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
            proposition: source_fact.clone(),
            proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
        }],
    }))
}

fn build_non_list_set_inferred_fact_proof(
    compiler: &LitexToLeanIrBuilder,
    source_fact: &Fact,
    source_fact_id: Option<FactId>,
    inferred_fact: &Fact,
    _reason: &str,
) -> Result<Option<LitexToLeanFactProofIr>, RuntimeError> {
    if let (Fact::AtomicFact(AtomicFact::InFact(source)), Some(source_fact_id)) =
        (source_fact, source_fact_id)
    {
        if let Obj::SetBuilder(builder) = &source.set {
            if let Fact::AtomicFact(AtomicFact::InFact(target)) = inferred_fact {
                if obj_equality_key(&source.element) == obj_equality_key(&target.element)
                    && obj_equality_key(builder.param_set.as_ref()) == obj_equality_key(&target.set)
                {
                    return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::SetBuilderBaseMembershipProjection,
                        parameter_requirements: Vec::new(),
                        premises: vec![LitexToLeanFactIr {
                            storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                            proposition: source_fact.clone(),
                            proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                        }],
                    });
                }
            }
            let mut substitutions = HashMap::new();
            insert_symbol_substitution(
                &mut substitutions,
                &builder.param_binding,
                source.element.clone(),
            );
            for (clause_index, clause) in builder.facts.iter().enumerate() {
                if !matches!(
                    clause,
                    QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(_))
                ) {
                    continue;
                }
                let instantiated = compiler
                    .instantiator
                    .inst_quantifier_free_fact(
                        clause,
                        &substitutions,
                        ParamObjType::SetBuilder,
                        Some(&inferred_fact.line_file()),
                    )
                    .map_err(|error| {
                        litex_to_lean_ir_error(
                            &inferred_fact.line_file(),
                            format!(
                                "could not replay set-builder predicate projection: {}",
                                error.trace_message()
                            ),
                        )
                    })?
                    .to_fact();
                if instantiated.to_string() == inferred_fact.to_string() {
                    return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::SetBuilderPredicateProjection {
                            clause_index,
                        },
                        parameter_requirements: Vec::new(),
                        premises: vec![LitexToLeanFactIr {
                            storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                            proposition: source_fact.clone(),
                            proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                        }],
                    });
                }
            }
        }
    }
    if let Some(source_fact_id) = source_fact_id {
        let components = match source_fact {
            Fact::AndFact(and_fact) => Some(
                and_fact
                    .facts
                    .iter()
                    .cloned()
                    .map(Fact::from)
                    .collect::<Vec<_>>(),
            ),
            Fact::ChainFact(chain_fact) => Some(
                chain_fact
                    .facts()?
                    .into_iter()
                    .map(Fact::from)
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        };
        if let Some(components) = components {
            if let Some(index) = components
                .iter()
                .position(|component| component.to_string() == inferred_fact.to_string())
            {
                return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ConjunctionProjection { index },
                    parameter_requirements: Vec::new(),
                    premises: vec![LitexToLeanFactIr {
                        storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                        proposition: source_fact.clone(),
                        proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                    }],
                });
            }
        }
    }
    if nonzero_numeric_membership_infers_nonzero(source_fact, inferred_fact) {
        if let Some(source_fact_id) = source_fact_id {
            return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::NonzeroNumericMembershipElimination,
                ),
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                }],
            });
        }
    }
    if positive_real_membership_infers_strict_positivity(source_fact, inferred_fact) {
        if let Some(source_fact_id) = source_fact_id {
            return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::PositiveRealMembership,
                ),
                parameter_requirements: Vec::new(),
                premises: vec![LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Stored(source_fact_id),
                    proposition: source_fact.clone(),
                    proof: LitexToLeanFactProofIr::KnownFactCitation { source_fact_id },
                }],
            });
        }
    }
    if matches!(
        inferred_fact,
        Fact::AtomicFact(AtomicFact::IsTupleFact(tuple))
            if matches!(&tuple.set, Obj::Tuple(tuple) if tuple.args.len() >= 2)
    ) {
        return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::TupleLiteralShape),
            parameter_requirements: Vec::new(),
            premises: Vec::new(),
        });
    }
    if let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(finite)) = inferred_fact {
        let rule = match &finite.set {
            Obj::ListSet(_) => Some(LitexToLeanFiniteSetBuiltinRuleIr::ListSet),
            Obj::Range(_) => Some(LitexToLeanFiniteSetBuiltinRuleIr::Range),
            Obj::ClosedRange(_) => Some(LitexToLeanFiniteSetBuiltinRuleIr::ClosedRange),
            _ => None,
        };
        if let Some(rule) = rule {
            return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::FiniteSet(rule)),
                parameter_requirements: Vec::new(),
                premises: Vec::new(),
            });
        }
    }
    if matches!(
        inferred_fact,
        Fact::AtomicFact(AtomicFact::EqualFact(equality))
            if obj_equality_key(&equality.left) == obj_equality_key(&equality.right)
    ) {
        return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::ObjectReflexivity,
            parameter_requirements: Vec::new(),
            premises: Vec::new(),
        });
    }
    if matches!(
        inferred_fact,
        Fact::AtomicFact(AtomicFact::EqualFact(equality))
            if crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                &equality.left,
                &equality.right,
            )
    ) {
        return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::RationalNormalization,
            parameter_requirements: Vec::new(),
            premises: Vec::new(),
        });
    }
    if crate::litex_to_lean_ir::is_closed_numeric_relation(inferred_fact) {
        return supported_inferred_proof(LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::ClosedNumericComparison,
            parameter_requirements: Vec::new(),
            premises: Vec::new(),
        });
    }
    Ok(None)
}

fn list_set_membership_inference_matches(
    source: &InFact,
    list_set: &ListSet,
    inferred: &Fact,
) -> bool {
    let expected = list_set
        .list
        .iter()
        .map(|item| {
            EqualFact::new_from_refs(&source.element, item.as_ref(), source.line_file.clone())
                .into()
        })
        .collect::<Vec<AtomicFact>>();
    if expected.len() == 1 {
        return matches!(inferred, Fact::AtomicFact(actual) if actual.to_string() == expected[0].to_string());
    }
    if expected.is_empty() {
        return false;
    }
    let Fact::OrFact(actual) = inferred else {
        return false;
    };
    actual.facts.len() == expected.len()
        && actual
            .facts
            .iter()
            .zip(expected.iter())
            .all(|(actual, expected)| actual.to_string() == expected.to_string())
}

fn supported_inferred_proof(
    proof: LitexToLeanFactProofIr,
) -> Result<Option<LitexToLeanFactProofIr>, RuntimeError> {
    Ok(Some(proof))
}

fn nonzero_numeric_membership_infers_nonzero(source_fact: &Fact, inferred_fact: &Fact) -> bool {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = source_fact else {
        return false;
    };
    if !matches!(
        membership.set,
        Obj::StandardSet(
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar
        )
    ) {
        return false;
    }
    let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = inferred_fact else {
        return false;
    };
    obj_equality_key(&nonzero.left) == obj_equality_key(&membership.element)
        && matches!(&nonzero.right, Obj::Number(number) if number.normalized_value == "0")
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
    infer_result: &SuccessInferResult,
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

fn explicit_proof_result_storage(
    infer_result: &SuccessInferResult,
    expected: &Fact,
) -> LitexToLeanFactStorageIr {
    let expected_text = expected.to_string();
    infer_result
        .store_fact_outputs
        .iter()
        .find(|output| output.itself_and_why_itself_is_stored.0.to_string() == expected_text)
        .and_then(|output| output.fact_id)
        .map(LitexToLeanFactStorageIr::Stored)
        .unwrap_or(LitexToLeanFactStorageIr::Anonymous)
}

fn added_fact_id_from_infer_result(
    infer_result: &SuccessInferResult,
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

fn build_litex_to_lean_ir_contradiction_pair(
    compiler: &LitexToLeanIrBuilder,
    impossible_check: &StmtResult,
    negated_impossible_check: &StmtResult,
    impossible_fact: &AtomicFact,
    context: &LitexToLeanIrConstructionContext,
) -> Result<LitexToLeanContradictionIr, RuntimeError> {
    let expected_fact: Fact = impossible_fact.clone().into();
    let expected_negation: Fact = impossible_fact.logical_negation()?.into();
    let mut fact = compiler.build_litex_to_lean_ir_fact_from_result(
        impossible_check,
        "impossible fact",
        context,
    )?;
    let mut negated_fact = compiler.build_litex_to_lean_ir_fact_from_result(
        negated_impossible_check,
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
    fact.make_anonymous();
    negated_fact.make_anonymous();
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

fn reverse_assumption_introduction_for_target(
    target: &Fact,
) -> LitexToLeanReverseAssumptionIntroductionIr {
    let target_is_negated = match target {
        Fact::AtomicFact(atomic) => matches!(
            atomic,
            AtomicFact::NotNormalAtomicFact(_)
                | AtomicFact::NotEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
                | AtomicFact::NotIsSetFact(_)
                | AtomicFact::NotIsNonemptySetFact(_)
                | AtomicFact::NotIsFiniteSetFact(_)
                | AtomicFact::NotInFact(_)
                | AtomicFact::NotIsCartFact(_)
                | AtomicFact::NotIsTupleFact(_)
                | AtomicFact::NotSubsetFact(_)
                | AtomicFact::NotSupersetFact(_)
        ),
        Fact::NotForall(_) => true,
        Fact::ExistFact(ExistFactEnum::NotExistFact(_)) => true,
        _ => false,
    };
    if target_is_negated {
        LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation
    } else {
        LitexToLeanReverseAssumptionIntroductionIr::DirectNegation
    }
}

#[cfg(test)]
mod fact_transformation_evidence_tests {
    use super::*;

    fn integer_membership(element: Obj) -> Fact {
        InFact::new(element, StandardSet::Z.into(), default_line_file()).into()
    }

    #[test]
    fn equality_rewrite_without_fact_id_fails_during_ir_capture() {
        let compiler = LitexToLeanIrBuilder::new();
        let source = integer_membership(Number::new("2".to_string()).into());
        let alias: Obj = Identifier::new("alias".to_string()).into();
        let target = integer_membership(alias.clone());
        let equality = EqualFact::new(
            alias.clone(),
            Number::new("2".to_string()).into(),
            default_line_file(),
        );
        let error = compiler
            .build_litex_to_lean_ir_equality_rewrite_fact(
                &target,
                LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Anonymous,
                    proposition: source,
                    proof: LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ClosedStandardMembership,
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
                    },
                },
                &EqualityTransportEvidence::new(vec![EqualityTransportStep::new(
                    Number::new("2".to_string()).into(),
                    alias,
                    equality,
                    None,
                )]),
            )
            .expect_err("missing equality provenance must fail before proof IR is produced");
        let message = error.trace_message();
        assert!(
            message.contains("no compiler proof provenance"),
            "{message}"
        );
    }

    #[test]
    fn fact_transformation_rejects_a_changed_source() {
        let compiler = LitexToLeanIrBuilder::new();
        let proved = integer_membership(Number::new("2".to_string()).into());
        let changed = integer_membership(Number::new("3".to_string()).into());
        let error = compiler
            .build_litex_to_lean_ir_fact_transformation(
                LitexToLeanFactIr {
                    storage: LitexToLeanFactStorageIr::Anonymous,
                    proposition: proved,
                    proof: LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ClosedStandardMembership,
                        parameter_requirements: Vec::new(),
                        premises: Vec::new(),
                    },
                },
                &FactTransformationEvidence::new(changed, Vec::new()),
            )
            .expect_err("a retargeted transformation source must fail during IR capture");
        let message = error.trace_message();
        assert!(
            message.contains("does not match proved premise"),
            "{message}"
        );
    }
}
