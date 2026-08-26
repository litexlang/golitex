use super::*;

impl StmtResultToLeanCompiler {
    /// Transitional direct entry point. It consumes one completed result at a
    /// time, so compiler state and declaration order already follow the result
    /// stream. Statement-family adapters are removed as their direct recursive
    /// compiler methods land.
    pub fn compile_stmt_results_to_lean_source(
        mut self,
        results: &[StmtResult],
    ) -> Result<String, String> {
        for (statement_index, result) in results.iter().enumerate() {
            self.compile_stmt_result(result).map_err(|error| {
                format!(
                    "statement Result {} failed to compile: {error}",
                    statement_index + 1
                )
            })?;
        }
        self.finish_lean_source()
    }

    /// Compile one completed execution Result into the compiler's declaration
    /// buffer. Final Lean source is assembled only after the full stream.
    pub(super) fn compile_stmt_result(&mut self, result: &StmtResult) -> Result<(), String> {
        match result {
            StmtResult::Success(success) => self.compile_success_stmt_result(success),
            StmtResult::Unknown(result) => Err(format!(
                "StmtResult-to-Lean compiler cannot compile unknown result: {result:?}"
            )),
        }
    }

    /// Declares the compilation responsibility of every statement family.
    ///
    /// A statement dispatcher is a `PassThrough`: it selects the matching
    /// family method but does not manufacture a compiler node. `Sketch` is a
    /// recursive `Combine`. The remaining currently supported families still
    /// use their focused compatibility adapter while their proof renderers are
    /// moved to consume the named Result fields directly.
    fn compile_success_stmt_result(&mut self, success: &SuccessStmtResult) -> Result<(), String> {
        match success {
            SuccessStmtResult::Fact(result) => self.compile_fact_stmt_result_to_lean_source(result),
            SuccessStmtResult::ReleaseThmStmt(result) => {
                if self.compile_litex_theorem_instantiation_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustStmt(result)) => {
                if self.compile_trust_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustHaveStmt(result)) => {
                if self.compile_trust_have_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::Definition(result) => match result {
                SuccessDefinitionStmtResult::LetObjStmt(result) => {
                    self.compile_let_obj_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(result) => {
                    self.compile_have_obj_in_nonempty_set_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::HaveObjEqualStmt(result) => {
                    self.compile_have_obj_equal_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::ObtainObjFromExistFact(result) => {
                    if self.compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveObjByExistFactsStmt(result) => {
                    if self.compile_have_obj_by_exist_facts_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(result) => {
                    if self
                        .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(result)?
                    {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveFnEqualStmt(result) => {
                    if self.compile_have_fn_equal_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveTupleStmt(result) => {
                    if self.compile_have_tuple_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveSeqStmt(result) => {
                    if self.compile_have_sequence_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveFiniteSeqStmt(result) => {
                    if self.compile_have_finite_sequence_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::HaveMatrixStmt(result) => {
                    if self.compile_have_matrix_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::ObtainObjFromThm(result) => {
                    if self.compile_obtain_obj_from_theorem_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        Err("StmtResultToLeanCompiler does not support this theorem-backed `obtain` Result shape".into())
                    }
                }
                SuccessDefinitionStmtResult::HaveByPreimageStmt(_)
                | SuccessDefinitionStmtResult::HaveFnEqualCaseByCaseStmt(_)
                | SuccessDefinitionStmtResult::HaveFnByInducStmt(_)
                | SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(_)
                | SuccessDefinitionStmtResult::HaveCartStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
                SuccessDefinitionStmtResult::DefPropStmt(result) => {
                    self.compile_def_prop_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::DefAbstractPropStmt(result) => {
                    self.compile_def_abstract_prop_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::DefSettingStmt(result) => {
                    self.compile_setting_definition_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::DefTemplateStmt(result) => {
                    self.compile_template_definition_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::DefStructStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
                SuccessDefinitionStmtResult::DefAlgoStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
                SuccessDefinitionStmtResult::DefThmStmt(result) => {
                    if self.compile_named_theorem_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessDefinitionStmtResult::AxiomStmt(result) => {
                    self.compile_source_axiom_stmt_result_to_lean_source(result)
                }
                SuccessDefinitionStmtResult::DefStrategyStmt(result) => {
                    self.compile_strategy_definition_stmt_result_to_lean_source(result)
                }
            },
            SuccessStmtResult::By(result) => match result {
                SuccessByStmtResult::ByCasesStmt(result) => {
                    if self.compile_by_cases_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByContraStmt(result) => {
                    if self.compile_by_contra_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByDefStmt(result) => {
                    if self.compile_by_definition_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByThmStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
                SuccessByStmtResult::ByReflexivePropStmt(result) => self
                    .compile_registered_predicate_property_stmt_result_to_lean_source(
                        &result.statement.forall_fact,
                        result.statement.proof.len(),
                        &result.common,
                        result.verification.as_ref(),
                        RegisteredPredicatePropertyCompilationKind::Reflexive,
                    ),
                SuccessByStmtResult::BySymmetricPropStmt(result) => self
                    .compile_registered_predicate_property_stmt_result_to_lean_source(
                        &result.statement.forall_fact,
                        result.statement.proof.len(),
                        &result.common,
                        result.verification.as_ref(),
                        RegisteredPredicatePropertyCompilationKind::Symmetric,
                    ),
                SuccessByStmtResult::ByTransitivePropStmt(result) => self
                    .compile_registered_predicate_property_stmt_result_to_lean_source(
                        &result.statement.forall_fact,
                        result.statement.proof.len(),
                        &result.common,
                        result.verification.as_ref(),
                        RegisteredPredicatePropertyCompilationKind::Transitive,
                    ),
                SuccessByStmtResult::ByAntisymmetricPropStmt(result) => self
                    .compile_registered_predicate_property_stmt_result_to_lean_source(
                        &result.statement.forall_fact,
                        result.statement.proof.len(),
                        &result.common,
                        result.verification.as_ref(),
                        RegisteredPredicatePropertyCompilationKind::Antisymmetric,
                    ),
                SuccessByStmtResult::ByExtensionStmt(result) => {
                    if self.compile_by_extension_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByEnumerateFiniteSetStmt(result) => {
                    if self.compile_by_enumerate_finite_set_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByForStmt(result) => {
                    if self.compile_by_for_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByEnumerateRangeStmt(result) => {
                    if self.compile_by_enumerate_range_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByClosedRangeAsCasesStmt(result) => {
                    if self.compile_by_closed_range_as_cases_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByInducStmt(result) => {
                    if self
                        .compile_structured_integer_induction_stmt_result_to_lean_source(result)?
                    {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessByStmtResult::ByFiniteSetInducStmt(_) => {
                    Err("finite-set induction Result compilation is not supported yet".into())
                }
                SuccessByStmtResult::ByZornLemmaStmt(_)
                | SuccessByStmtResult::ByAxiomOfChoiceStmt(_)
                | SuccessByStmtResult::ByRegularityAxiomStmt(_)
                | SuccessByStmtResult::ByStructDefStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
            },
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessExistFact(result)) => {
                if self.compile_witness_exist_fact_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessAtomicFact(result)) => {
                if self.compile_witness_atomic_fact_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessNonemptySet(result)) => {
                if self.compile_witness_nonempty_set_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.unsupported_success_stmt_result(success)
                }
            }
            SuccessStmtResult::ProofBlock(result) => match result {
                SuccessProofBlockStmtResult::ClaimStmt(result) => {
                    if self.compile_claim_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessProofBlockStmtResult::ExampleStmt(result) => {
                    if self.compile_example_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                SuccessProofBlockStmtResult::SketchStmt(result) => {
                    self.compile_sketch_stmt_result_to_lean_source(result)
                }
                SuccessProofBlockStmtResult::TryStmt(result) => {
                    self.compile_try_stmt_result_to_lean_source(result)
                }
            },
            SuccessStmtResult::Command(SuccessCommandStmtResult::EvalStmt(result)) => {
                self.compile_eval_stmt_result_to_lean_source(result)
            }
            SuccessStmtResult::Command(SuccessCommandStmtResult::ImportStmt(_)) => {
                self.unsupported_success_stmt_result(success)
            }
        }
    }

    fn unsupported_success_stmt_result(&self, result: &SuccessStmtResult) -> Result<(), String> {
        let statement = result.statement();
        Err(format!(
            "StmtResult-to-Lean compiler does not support statement kind `{}` at {:?}",
            statement.stmt_type_name(),
            statement.line_file()
        ))
    }
}
