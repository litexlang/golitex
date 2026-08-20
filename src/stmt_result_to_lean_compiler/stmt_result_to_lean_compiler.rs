use super::stmt_result_to_lean_compiler_environment_stack::*;
use crate::litex_to_lean_ir::{
    LitexToLeanIrBuilder, ADD_NONNEGATIVE_FINGERPRINT, ADD_NONNEGATIVE_RULE_ID,
    ADD_POSITIVE_FINGERPRINT, ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT,
    ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID, ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT,
    ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID, ADD_POSITIVE_RULE_ID,
    DIV_NONNEGATIVE_FINGERPRINT, DIV_NONNEGATIVE_RULE_ID, DIV_POSITIVE_FINGERPRINT,
    DIV_POSITIVE_RULE_ID, LESS_EQUAL_OF_LESS_FINGERPRINT, LESS_EQUAL_OF_LESS_RULE_ID,
    MUL_NONNEGATIVE_FINGERPRINT, MUL_NONNEGATIVE_RULE_ID, MUL_POSITIVE_FINGERPRINT,
    MUL_POSITIVE_RULE_ID, SET_EMPTY_SUBSET_FINGERPRINT, SET_EMPTY_SUBSET_RULE_ID,
    SET_INTERSECT_ASSOCIATIVE_FINGERPRINT, SET_INTERSECT_ASSOCIATIVE_RULE_ID,
    SET_INTERSECT_COMMUTATIVE_FINGERPRINT, SET_INTERSECT_COMMUTATIVE_RULE_ID,
    SET_INTERSECT_EQ_LEFT_OF_SUBSET_FINGERPRINT, SET_INTERSECT_EQ_LEFT_OF_SUBSET_RULE_ID,
    SET_INTERSECT_EQ_RIGHT_OF_SUBSET_FINGERPRINT, SET_INTERSECT_EQ_RIGHT_OF_SUBSET_RULE_ID,
    SET_INTERSECT_FINITE_FINGERPRINT, SET_INTERSECT_FINITE_RULE_ID,
    SET_INTERSECT_MEMBERSHIP_FINGERPRINT, SET_INTERSECT_MEMBERSHIP_RULE_ID,
    SET_INTERSECT_SUBSET_LEFT_FINGERPRINT, SET_INTERSECT_SUBSET_LEFT_RULE_ID,
    SET_INTERSECT_SUBSET_RIGHT_FINGERPRINT, SET_INTERSECT_SUBSET_RIGHT_RULE_ID,
    SET_INTERSECT_UNION_DISTRIBUTIVE_FINGERPRINT, SET_INTERSECT_UNION_DISTRIBUTIVE_RULE_ID,
    SET_MINUS_FINITE_LEFT_FINGERPRINT, SET_MINUS_FINITE_LEFT_RULE_ID,
    SET_MINUS_INTERSECT_DE_MORGAN_FINGERPRINT, SET_MINUS_INTERSECT_DE_MORGAN_RULE_ID,
    SET_MINUS_MEMBERSHIP_FINGERPRINT, SET_MINUS_MEMBERSHIP_RULE_ID,
    SET_MINUS_RECOVER_SUBSET_FINGERPRINT, SET_MINUS_RECOVER_SUBSET_RULE_ID,
    SET_MINUS_SUBSET_LEFT_FINGERPRINT, SET_MINUS_SUBSET_LEFT_RULE_ID,
    SET_MINUS_UNION_DE_MORGAN_FINGERPRINT, SET_MINUS_UNION_DE_MORGAN_RULE_ID,
    SET_POWER_SET_FINITE_FINGERPRINT, SET_POWER_SET_FINITE_RULE_ID,
    SET_POWER_SET_MEMBERSHIP_OF_SUBSET_FINGERPRINT, SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID,
    SET_POWER_SET_NONEMPTY_FINGERPRINT, SET_POWER_SET_NONEMPTY_RULE_ID,
    SET_SUBSET_EQ_SET_MINUS_RECOVERY_FINGERPRINT, SET_SUBSET_EQ_SET_MINUS_RECOVERY_RULE_ID,
    SET_SUBSET_UNION_LEFT_FINGERPRINT, SET_SUBSET_UNION_LEFT_RULE_ID,
    SET_SUBSET_UNION_RIGHT_FINGERPRINT, SET_SUBSET_UNION_RIGHT_RULE_ID,
    SET_UNION_ASSOCIATIVE_FINGERPRINT, SET_UNION_ASSOCIATIVE_RULE_ID,
    SET_UNION_COMMUTATIVE_FINGERPRINT, SET_UNION_COMMUTATIVE_RULE_ID,
    SET_UNION_EMPTY_LEFT_FINGERPRINT, SET_UNION_EMPTY_LEFT_RULE_ID,
    SET_UNION_EMPTY_RIGHT_FINGERPRINT, SET_UNION_EMPTY_RIGHT_RULE_ID, SET_UNION_FINITE_FINGERPRINT,
    SET_UNION_FINITE_RULE_ID, SET_UNION_IDEMPOTENT_FINGERPRINT, SET_UNION_IDEMPOTENT_RULE_ID,
    SET_UNION_MEMBERSHIP_LEFT_FINGERPRINT, SET_UNION_MEMBERSHIP_LEFT_RULE_ID,
    SET_UNION_MEMBERSHIP_RIGHT_FINGERPRINT, SET_UNION_MEMBERSHIP_RIGHT_RULE_ID,
    SET_UNION_NONEMPTY_LEFT_FINGERPRINT, SET_UNION_NONEMPTY_LEFT_RULE_ID,
    SET_UNION_NONEMPTY_RIGHT_FINGERPRINT, SET_UNION_NONEMPTY_RIGHT_RULE_ID,
    SET_UNION_SUBSET_FINGERPRINT, SET_UNION_SUBSET_RULE_ID,
};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::mem;
use std::path::Path;

/// Compiles the recursive output of Litex statement execution into Lean source.
///
/// The compiler owns a stack of Lean-generation environments in the same way
/// that [`Runtime`] owns execution environments. The stack contains generated
/// names and source fragments only; all proof evidence comes from `StmtResult`.
pub struct StmtResultToLeanCompiler {
    source_label: String,
    environment_stack: StmtResultToLeanCompilerEnvironmentStack,
    declarations: Vec<String>,
    next_fact_name_index: usize,
    next_sketch_namespace_index: usize,
}

struct CompiledOrdinaryFactGoalProofBody {
    local_proof_lines: Vec<String>,
    proposition: String,
    conclusion_proof: String,
}

struct CompiledNamedTheoremProofBody {
    binder_declarations: Vec<String>,
    binder_intro_names: Vec<String>,
    proof_lines: Vec<String>,
    conclusion_type: String,
}

struct CompiledExistentialWitnessProofBody {
    proposition: String,
    proof_expression: String,
}

struct CompiledFactProofBody {
    fact: Fact,
    proposition: String,
    proof_expression: String,
}

struct CompiledByDefinitionComponentProofBody {
    fact: Fact,
    retained_fact_id: Option<FactId>,
    proposition: String,
    proof_expression: String,
}

struct CompiledByDefinitionProofBody {
    target: CompiledFactProofBody,
    components: Vec<CompiledByDefinitionComponentProofBody>,
}

struct CompiledLitexTheoremInstantiationConclusionProofBody {
    retained_fact_id: Option<FactId>,
    fact: Fact,
    proposition: String,
    proof_expression: String,
}

/// Target-language construction output for one reviewed native-real function
/// Result. This is not another statement IR: it exists only while the parent
/// `SuccessHaveFnEqualStmtResult` method wraps its child-scope compilation in
/// persistent Lean declarations.
struct CompiledNamedRealFunctionDefinitionBody {
    function: LitexToLeanFunctionTypeIr,
    source_body: Obj,
    lowered_body: LitexToLeanObjectIr,
    value: String,
    parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
    domain_premises: Vec<LitexToLeanLocalPremiseIr>,
}

/// Target-language construction output returned from the tuple index scope.
/// The recursive WD Result remains owned by the statement result; this value
/// contains only what the parent needs after the compiler environment pops.
struct CompiledIndexedTupleDefinitionBody {
    dimension: usize,
    value: String,
    positive_dimension_proof: String,
    at_least_two_dimension_proof: String,
}

/// Target-language construction output returned from one indexed-function
/// child scope. Sequence, finite-sequence, and matrix Results differ only in
/// how many parameter and domain premises their nested scopes publish, so the
/// parent compiler consumes one common shape instead of three parallel
/// temporary structures.
struct CompiledIndexedFunctionDefinitionBody {
    function: LitexToLeanFunctionTypeIr,
    source_body: Obj,
    lowered_body: LitexToLeanObjectIr,
    value: String,
    parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
    domain_premises: Vec<LitexToLeanLocalPremiseIr>,
}

impl StmtResultToLeanCompiler {
    pub fn new(source_label: &str) -> Self {
        Self {
            source_label: source_label.to_string(),
            environment_stack: StmtResultToLeanCompilerEnvironmentStack::default(),
            declarations: Vec::new(),
            next_fact_name_index: 0,
            next_sketch_namespace_index: 0,
        }
    }

    /// Transitional direct entry point. It consumes one completed result at a
    /// time, so compiler state and declaration order already follow the result
    /// stream. Statement-family adapters are removed as their direct recursive
    /// compiler methods land.
    pub fn compile_stmt_results_to_lean_source(
        mut self,
        results: &[StmtResult],
    ) -> Result<String, String> {
        for result in results {
            self.compile_stmt_result_to_lean_source(result)?;
        }
        self.finish_lean_source()
    }

    fn compile_stmt_result_to_lean_source(&mut self, result: &StmtResult) -> Result<(), String> {
        match result {
            StmtResult::Success(success) => {
                self.compile_success_stmt_result_to_lean_source(success, result)
            }
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
    fn compile_success_stmt_result_to_lean_source(
        &mut self,
        success: &SuccessStmtResult,
        complete_result: &StmtResult,
    ) -> Result<(), String> {
        match success {
            SuccessStmtResult::Fact(result) => self.compile_fact_stmt_result_to_lean_source(result),
            SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustStmt(result)) => {
                if self.compile_trust_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.compile_compatibility_statement_result_to_lean_source(complete_result)
                }
            }
            SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustHaveStmt(_)) => {
                self.unsupported_success_stmt_result(success)
            }
            SuccessStmtResult::DefObjStmt(result) => match result {
                SuccessDefObjStmtResult::LetObjStmt(result) => {
                    self.compile_let_obj_stmt_result_to_lean_source(result)
                }
                SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(result) => {
                    self.compile_have_obj_in_nonempty_set_stmt_result_to_lean_source(result)
                }
                SuccessDefObjStmtResult::HaveObjEqualStmt(result) => {
                    self.compile_have_obj_equal_stmt_result_to_lean_source(result)
                }
                SuccessDefObjStmtResult::ObtainObjFromExistFact(result) => {
                    if self.compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveObjByExistFactsStmt(result) => {
                    if self.compile_have_obj_by_exist_facts_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::ObtainObjFromAtomicFact(result) => {
                    if self
                        .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(result)?
                    {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveFnEqualStmt(result) => {
                    if self.compile_have_fn_equal_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveTupleStmt(result) => {
                    if self.compile_have_tuple_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveSeqStmt(result) => {
                    if self.compile_have_sequence_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveFiniteSeqStmt(result) => {
                    if self.compile_have_finite_sequence_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::HaveMatrixStmt(result) => {
                    if self.compile_have_matrix_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessDefObjStmtResult::ObtainObjFromThm(result) => {
                    if self.compile_obtain_obj_from_theorem_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        Err("StmtResultToLeanCompiler does not support this theorem-backed `obtain` Result shape".into())
                    }
                }
                SuccessDefObjStmtResult::HaveByPreimageStmt(_)
                | SuccessDefObjStmtResult::HaveFnEqualCaseByCaseStmt(_)
                | SuccessDefObjStmtResult::HaveFnByInducStmt(_)
                | SuccessDefObjStmtResult::HaveFnByForallExistUniqueStmt(_)
                | SuccessDefObjStmtResult::HaveCartStmt(_) => {
                    self.unsupported_success_stmt_result(success)
                }
            },
            SuccessStmtResult::DefPredicateStmt(result) => match result {
                SuccessDefPredicateStmtResult::DefPropStmt(result) => {
                    self.compile_def_prop_stmt_result_to_lean_source(result)
                }
                SuccessDefPredicateStmtResult::DefAbstractPropStmt(result) => {
                    self.compile_def_abstract_prop_stmt_result_to_lean_source(result)
                }
            },
            SuccessStmtResult::DefInterfaceStmt(_)
            | SuccessStmtResult::DefAlgoStmt(_)
            | SuccessStmtResult::AxiomStmt(_)
            | SuccessStmtResult::DefStrategyStmt(_) => {
                self.unsupported_success_stmt_result(success)
            }
            SuccessStmtResult::DefThmStmt(result) => {
                if self.compile_named_theorem_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.compile_compatibility_statement_result_to_lean_source(complete_result)
                }
            }
            SuccessStmtResult::By(result) => match result {
                SuccessByStmtResult::ByCasesStmt(result) => {
                    if self.compile_by_cases_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessByStmtResult::ByContraStmt(result) => {
                    if self.compile_by_contra_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessByStmtResult::ByDefStmt(result) => {
                    if self.compile_by_definition_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessByStmtResult::ByThmStmt(result) => {
                    if self
                        .compile_litex_theorem_instantiation_stmt_result_to_lean_source(result)?
                    {
                        Ok(())
                    } else {
                        self.unsupported_success_stmt_result(success)
                    }
                }
                _ => self.unsupported_success_stmt_result(success),
            },
            SuccessStmtResult::Witness(SuccessWitnessStmtResult::WitnessExistFact(result)) => {
                if self.compile_witness_exist_fact_stmt_result_to_lean_source(result)? {
                    Ok(())
                } else {
                    self.compile_compatibility_statement_result_to_lean_source(complete_result)
                }
            }
            SuccessStmtResult::Witness(_) => self.unsupported_success_stmt_result(success),
            SuccessStmtResult::ProofBlock(result) => match result {
                SuccessProofBlockStmtResult::ClaimStmt(result) => {
                    if self.compile_claim_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessProofBlockStmtResult::ExampleStmt(result) => {
                    if self.compile_example_stmt_result_to_lean_source(result)? {
                        Ok(())
                    } else {
                        self.compile_compatibility_statement_result_to_lean_source(complete_result)
                    }
                }
                SuccessProofBlockStmtResult::SketchStmt(result) => {
                    self.compile_sketch_stmt_result_to_lean_source(result)
                }
                SuccessProofBlockStmtResult::TryStmt(result) => {
                    self.compile_try_stmt_result_to_lean_source(result)
                }
            },
            SuccessStmtResult::Command(SuccessCommandStmtResult::DoNothingStmt(result)) => {
                self.compile_do_nothing_stmt_result_to_lean_source(result)
            }
            SuccessStmtResult::Command(_) => self.unsupported_success_stmt_result(success),
        }
    }

    fn compile_have_obj_in_nonempty_set_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjInNonemptySetStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "object choice has no structured nonemptiness-to-membership result".to_string()
        })?;
        let parameter_groups = &result.statement.param_def.groups;
        if parameter_groups.len() != verification.groups.len() {
            return Err("object choice changed its parameter-group mapping".into());
        }
        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.iter().any(|store| {
                !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty()
            })
        {
            return Err("object choice retained unsupported inferred consequences".into());
        }

        let expected_choice_count = parameter_groups
            .iter()
            .map(|group| group.params.len())
            .sum::<usize>();
        if result.common.infers.store_fact_outputs.len() != expected_choice_count {
            return Err("object choice store count does not match its selected objects".into());
        }

        for (parameter_group, verified_group) in
            parameter_groups.iter().zip(verification.groups.iter())
        {
            let carrier = parameter_set(&parameter_group.param_type)?;
            if parameter_group.params.len() != verified_group.selected_type_facts.len() {
                return Err("object choice changed its binding-to-membership mapping".into());
            }
            let nonempty_check = verified_group.nonempty_check.as_deref().ok_or_else(|| {
                "object-carrier choice retained no nonemptiness proof".to_string()
            })?;
            let nonempty_proof = compile_standard_set_nonempty_fact_proof_from_result(
                nonempty_check,
                carrier,
                &self.environment_stack,
            )?;
            let rendered_carrier = render_obj(carrier, &self.environment_stack)?;

            for (binding, selected_type_fact) in parameter_group
                .params
                .iter()
                .zip(verified_group.selected_type_facts.iter())
            {
                let source_name = binding.name();
                let lean_name = lean_identifier(source_name);
                let defined_object: Obj =
                    Identifier::new_bound(source_name.to_string(), binding.as_ref()).into();
                let expected_membership: Fact = InFact::new(
                    defined_object,
                    carrier.clone(),
                    result.statement.line_file.clone(),
                )
                .into();
                if selected_type_fact.to_string() != expected_membership.to_string() {
                    return Err(format!(
                        "object choice changed selected membership `{selected_type_fact}`"
                    ));
                }
                let matching_stores = result
                    .common
                    .infers
                    .store_fact_outputs
                    .iter()
                    .filter(|store| {
                        store.itself_and_why_itself_is_stored.0.to_string()
                            == selected_type_fact.to_string()
                    })
                    .collect::<Vec<_>>();
                let [store] = matching_stores.as_slice() else {
                    return Err(
                        "object choice membership does not have exactly one store effect".into(),
                    );
                };
                let fact_id = store
                    .fact_id
                    .ok_or_else(|| "object choice membership has no FactId".to_string())?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{source_name}`"
                    ));
                }
                self.declarations.push(format!(
                    "noncomputable def {lean_name} : {rendered_carrier}.Carrier :=\n  Classical.choice ({nonempty_proof})"
                ));

                let proposition = render_fact(selected_type_fact, &self.environment_stack)?;
                let theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {theorem_name} : {proposition} := by\n  exact Litex.In.own {rendered_carrier} {lean_name}"
                ));
                self.environment_stack
                    .fact_names
                    .insert(fact_id, theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, selected_type_fact.clone());
                self.next_fact_name_index += 1;
            }
        }
        Ok(())
    }

    fn compile_have_obj_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjEqualStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "have-object equality has no structured value type-check results".to_string()
        })?;
        let bindings_with_types = result
            .statement
            .param_def
            .collect_param_bindings_with_types();
        if bindings_with_types.len() != result.statement.objs_equal_to.len()
            || bindings_with_types.len() != verification.type_checks.len()
        {
            return Err(
                "have-object equality changed its binding, value, or type-check count".into(),
            );
        }
        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
        {
            return Err("have-object equality retained unsupported inferred consequences".into());
        }

        let mut expected_stored_facts = Vec::with_capacity(bindings_with_types.len() * 2);
        for ((binding, param_type), value) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
        {
            let defined_object: Obj =
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
            expected_stored_facts.push(object_type_fact_for_compiler_definition(
                defined_object.clone(),
                param_type,
                result.statement.line_file.clone(),
            ));
            expected_stored_facts.push(
                EqualFact::new(
                    defined_object,
                    value.clone(),
                    result.statement.line_file.clone(),
                )
                .into(),
            );
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &expected_stored_facts,
            "have-object equality",
        )?;

        for (index, ((binding, param_type), value)) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
            .enumerate()
        {
            let expected_value_type = object_type_fact_for_compiler_definition(
                value.clone(),
                param_type,
                result.statement.line_file.clone(),
            );
            let type_check = verification.type_checks[index]
                .factual_success()
                .ok_or_else(|| {
                    format!(
                        "have-object value `{}` has no successful type-check child Result",
                        binding.name()
                    )
                })?;
            if type_check.fact().to_string() != expected_value_type.to_string() {
                return Err(format!(
                    "have-object value type-check changed `{expected_value_type}` to `{}`",
                    type_check.fact()
                ));
            }

            let lean_name = lean_identifier(binding.name());
            if matches!(param_type, ParamType::Set(_)) {
                let lowered_value = LitexToLeanObjectIr::lower(value)?;
                let rendered_value =
                    render_set_definition_value(&lowered_value, &self.environment_stack)?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{}`",
                        binding.name()
                    ));
                }
                self.declarations.push(format!(
                    "abbrev {lean_name} : Litex.Set := {rendered_value}"
                ));
                continue;
            }

            let ParamType::Obj(_) = param_type else {
                return Err(format!(
                    "have-object `{}` has an unsupported non-membership type",
                    binding.name()
                ));
            };
            if bindings_with_types.len() != 1 {
                return Err(
                    "native have-object definitions currently require exactly one object".into(),
                );
            }
            let lowered_value = LitexToLeanObjectIr::lower(value)?;
            let rendered_value = render_native_object_ir(&lowered_value, &self.environment_stack)?;
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), lean_name.clone())
                .is_some()
            {
                return Err(format!(
                    "duplicate compiler symbol identity for `{}`",
                    binding.name()
                ));
            }
            self.declarations
                .push(format!("noncomputable def {lean_name} := {rendered_value}"));

            let type_check_proof =
                construct_lean_proof_for_compatibility_fact_result_without_storing(
                    &verification.type_checks[index],
                    &expected_value_type,
                    &self.environment_stack,
                )?;
            let stored_type_fact = expected_stored_facts[index * 2].clone();
            let stored_equality = expected_stored_facts[index * 2 + 1].clone();
            let stored_type_fact_id = stored_fact_ids[index * 2];
            let stored_equality_fact_id = stored_fact_ids[index * 2 + 1];
            let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
            let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;

            let type_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {type_theorem_name} : {rendered_type_fact} := by\n  unfold {lean_name}\n  exact {type_check_proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_type_fact_id, type_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_type_fact_id, stored_type_fact);
            self.next_fact_name_index += 1;

            let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {equality_theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_equality_fact_id, equality_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_equality_fact_id, stored_equality);
            self.next_fact_name_index += 1;
        }
        Ok(())
    }

    /// `Combine`: a named function Result first enters the anonymous
    /// function's binder environment, installs the exact temporary FactIds
    /// retained by `assumption_infers`, consumes the recursive return-check
    /// Result there, and only then returns to the parent environment to
    /// publish the membership/equality FactIds.
    ///
    /// The first direct slice is intentionally semantic rather than syntactic:
    /// every parameter and the codomain must be `R`, while unary/domain and
    /// multi-parameter telescope shapes are both supported. Other codomains
    /// continue through the compatibility adapter until their representative
    /// selection Result paths are migrated.
    fn compile_have_fn_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFnEqualStmtResult,
    ) -> Result<bool, String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "named function has no structured body-to-environment verification Result".to_string()
        })?;
        let statement = &result.statement;
        let function_set = FnSet::from_body(statement.equal_to_anonymous_fn.body.clone())
            .map_err(|error| error.to_string())?;
        let function = LitexToLeanFunctionTypeIr::lower(&function_set)?;
        let is_native_real_signature = function.parameters.iter().all(|parameter| {
            parameter.set == LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
        }) && function.return_set.as_ref()
            == &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real);
        if !is_native_real_signature {
            return Ok(false);
        }

        let source_body = statement.equal_to_anonymous_fn.equal_to.as_ref().clone();
        let lowered_body = LitexToLeanObjectIr::lower(&source_body)?;
        let source_return_set = statement
            .equal_to_anonymous_fn
            .body
            .ret_set
            .as_ref()
            .clone();
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            source_return_set,
            statement.line_file.clone(),
        )
        .into();

        let mut expected_parameter_facts = Vec::new();
        for group in statement
            .equal_to_anonymous_fn
            .body
            .params_def_with_set
            .iter()
        {
            expected_parameter_facts.extend(group.facts_for_binding_scope(ParamObjType::FnSet));
        }
        let expected_domain_facts = statement
            .equal_to_anonymous_fn
            .body
            .dom_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if expected_parameter_facts.len() != function.parameters.len()
            || expected_domain_facts.len() != function.domain_facts.len()
        {
            return Err("named real function changed its parameter/domain Result mapping".into());
        }
        if !verification.assumption_infers.rule_applications.is_empty()
            || verification
                .assumption_infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let mut expected_assumptions = expected_parameter_facts.clone();
        expected_assumptions.extend(expected_domain_facts.iter().cloned());
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            &verification.assumption_infers,
            &expected_assumptions,
            "named real function local assumptions",
        )?;
        let (parameter_fact_ids, domain_fact_ids) =
            assumption_fact_ids.split_at(expected_parameter_facts.len());

        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_membership: Fact = InFact::new(
            function_object.clone(),
            function_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object,
            statement.equal_to_anonymous_fn.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if verification.function_membership.to_string() != expected_membership.to_string()
            || verification.defining_equality.to_string() != expected_defining_equality.to_string()
        {
            return Err(
                "named real function verification changed its outer membership/equality".into(),
            );
        }
        if !result.common.infers.rule_applications.is_empty()
            || result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &[
                expected_membership.clone(),
                expected_defining_equality.clone(),
            ],
            "named real function outer effects",
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<Option<CompiledNamedRealFunctionDefinitionBody>, String> =
            (|| {
                let mut parameter_premises = Vec::with_capacity(function.parameters.len());
                for (parameter_index, ((parameter, fact), fact_id)) in function
                    .parameters
                    .iter()
                    .zip(expected_parameter_facts.iter())
                    .zip(parameter_fact_ids.iter())
                    .enumerate()
                {
                    let suffix = if function_uses_telescope(&function) {
                        (parameter_index + 1).to_string()
                    } else {
                        String::new()
                    };
                    let argument_name = format!("__arg{suffix}");
                    let membership_name = format!("__arg{suffix}_in");
                    if self
                        .environment_stack
                        .symbol_names
                        .insert(parameter.symbol_id, argument_name.clone())
                        .is_some()
                    {
                        return Err("named real function reused one parameter SymbolId".into());
                    }
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, membership_name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, fact.clone());
                    if let Some(real) =
                        membership_real_value(&parameter.set, &argument_name, &membership_name)
                    {
                        self.environment_stack
                            .numeric_real_values
                            .insert(parameter.symbol_id, real);
                    }
                    if let Some(representation) =
                        membership_numeric_value(&parameter.set, &argument_name, &membership_name)
                    {
                        self.environment_stack
                            .numeric_representations
                            .insert(parameter.symbol_id, representation);
                    }
                    if let Some(proof) =
                        membership_numeric_proof(&parameter.set, &argument_name, &membership_name)
                    {
                        self.environment_stack
                            .numeric_representation_memberships
                            .insert(parameter.symbol_id, proof);
                    }
                    parameter_premises.push(LitexToLeanLocalPremiseIr::new(*fact_id, fact.clone()));
                }

                let mut domain_premises = Vec::with_capacity(expected_domain_facts.len());
                for (domain_index, (fact, fact_id)) in expected_domain_facts
                    .iter()
                    .zip(domain_fact_ids.iter())
                    .enumerate()
                {
                    let selector = conjunction_selector(domain_index, expected_domain_facts.len())?;
                    let proof_name = if expected_domain_facts.len() == 1 {
                        "__arg_domain".to_string()
                    } else {
                        format!("__arg_domain{selector}")
                    };
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, proof_name);
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, fact.clone());
                    domain_premises.push(LitexToLeanLocalPremiseIr::new(*fact_id, fact.clone()));
                }

                let return_check = verification
                    .return_check
                    .factual_success()
                    .ok_or_else(|| "named real function return check is not factual".to_string())?;
                if return_check.fact().to_string() != expected_return_check.to_string()
                    || return_check.store.fact.to_string() != expected_return_check.to_string()
                    || !return_check.store.infers.is_empty()
                {
                    return Err(
                        "named real function changed or published effects from its local return check"
                            .into(),
                    );
                }
                if self
                    .construct_lean_proof_from_direct_fact_result(return_check)?
                    .is_none()
                {
                    return Err(
                        "named real function return check has no direct recursive Result proof adapter"
                            .into(),
                    );
                }
                let value = render_named_real_function_value_from_result(
                    &function,
                    &lowered_body,
                    &self.environment_stack,
                )?;
                Ok(Some(CompiledNamedRealFunctionDefinitionBody {
                    function: function.clone(),
                    source_body: source_body.clone(),
                    lowered_body: lowered_body.clone(),
                    value,
                    parameter_premises,
                    domain_premises,
                }))
            })();
        self.environment_stack.pop_local_environment();
        let Some(compiled_body) = compiled_body? else {
            return Ok(false);
        };

        let name = lean_identifier(statement.name());
        let function_value_name = if function_uses_telescope(&compiled_body.function) {
            format!("(@{name})")
        } else {
            name.clone()
        };
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let function_set = render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let membership_name = format!("__fact{}", self.next_fact_name_index);
        let membership_proposition = render_fact(&expected_membership, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem {membership_name} : {membership_proposition} := by\n  exact Litex.In.own {function_set} {function_value_name}"
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[0], membership_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[0], expected_membership);
        self.environment_stack.function_bindings.insert(
            stored_fact_ids[0],
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: membership_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_name = format!("__fact{}", self.next_fact_name_index);
        let equality_proposition = format!(
            "Litex.Same {function_value_name} ({} : {function_type})",
            compiled_body.value
        );
        self.declarations.push(format!(
            "theorem {equality_name} : {equality_proposition} := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[1], equality_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[1], expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            stored_fact_ids[1],
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                uses_native_real_body: true,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                compatibility_return_selection: None,
                well_definedness: LitexToLeanWellDefinednessCertificateIr::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: compile the two retained dimension checks in the ambient
    /// environment, compile the coordinate value under its exact index
    /// binder, pop that child environment, then publish the three ordered
    /// tuple-definition store effects.
    fn compile_have_tuple_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveTupleStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let lowered_dimension = LitexToLeanObjectIr::lower(&statement.dimension)?;
        let LitexToLeanObjectIr::Number {
            normalized_value: normalized_dimension,
        } = &lowered_dimension
        else {
            return Ok(false);
        };
        let dimension = normalized_dimension
            .parse::<usize>()
            .map_err(|_| "indexed tuple dimension is not a machine natural".to_string())?;
        if dimension < 2 {
            return Err("indexed tuple dimension is smaller than two".into());
        }

        let expected_positive_dimension: Fact = InFact::new(
            statement.dimension.clone(),
            StandardSet::NPos.into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_at_least_two: Fact = LessEqualFact::new(
            Number::new("2".to_string()).into(),
            statement.dimension.clone(),
            statement.line_file.clone(),
        )
        .into();
        let positive_dimension = verification
            .dimension
            .positive_check
            .factual_success()
            .ok_or_else(|| "indexed tuple positive-dimension check is not factual".to_string())?;
        let at_least_two = verification
            .dimension
            .at_least_two_check
            .factual_success()
            .ok_or_else(|| "indexed tuple at-least-two check is not factual".to_string())?;
        for (check, expected, role) in [
            (
                positive_dimension,
                &expected_positive_dimension,
                "positive-dimension",
            ),
            (at_least_two, &expected_at_least_two, "at-least-two"),
        ] {
            if check.fact().to_string() != expected.to_string()
                || check.store.fact.to_string() != expected.to_string()
                || !check.store.infers.is_empty()
            {
                return Err(format!(
                    "indexed tuple {role} Result changed its target or published effects"
                ));
            }
        }
        let Some(positive_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(positive_dimension)?
        else {
            return Ok(false);
        };
        let Some(at_least_two_dimension_proof) =
            self.construct_lean_proof_from_direct_fact_result(at_least_two)?
        else {
            return Ok(false);
        };

        let lowered_value = LitexToLeanObjectIr::lower(&statement.value)?;
        if !indexed_tuple_value_is_complex(&lowered_value, statement.index_binding.id()) {
            return Ok(false);
        }
        let mut visited = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.value_well_definedness.as_ref(),
            &statement.value,
            &mut visited,
        )?;

        self.environment_stack.push_inherited_environment();
        let compiled_body = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__index".into());
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "(((__index.val : ℤ) : ℂ))".into(),
            );
            let mut installed_well_definedness_nodes = HashSet::new();
            install_object_well_definedness_store_results(
                verification.value_well_definedness.as_ref(),
                &mut self.environment_stack,
                &mut installed_well_definedness_nodes,
            )?;
            let value = render_numeric_object_ir(&lowered_value, &self.environment_stack)?;
            Ok::<_, String>(CompiledIndexedTupleDefinitionBody {
                dimension,
                value,
                positive_dimension_proof,
                at_least_two_dimension_proof,
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("indexed tuple stores retained unexpected typed infer rules".into());
        }
        let [is_tuple_output, dimension_output, coordinate_output] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("indexed tuple requires exactly three ordered store outputs".into());
        };
        for output in [is_tuple_output, dimension_output, coordinate_output] {
            if output.fact_id.is_none()
                || !output.inferred_facts.is_empty()
                || !output.inferred_fact_ids.is_empty()
            {
                return Err(
                    "indexed tuple store output lost its FactId or gained inferred children".into(),
                );
            }
        }

        let name = lean_identifier(statement.name());
        let positive_dimension_proposition =
            render_fact(&expected_positive_dimension, &self.environment_stack)?;
        let at_least_two_proposition =
            render_fact(&expected_at_least_two, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem __{name}_dimension_check1 : {positive_dimension_proposition} := by\n  exact {}",
            compiled_body.positive_dimension_proof
        ));
        self.declarations.push(format!(
            "theorem __{name}_dimension_check2 : {at_least_two_proposition} := by\n  exact {}",
            compiled_body.at_least_two_dimension_proof
        ));
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.IndexedTuple {} ℂ :=\n  ⟨fun __index => {}⟩",
            compiled_body.dimension, compiled_body.value
        ));
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for indexed tuple `{}`",
                statement.name()
            ));
        }
        self.environment_stack.indexed_tuple_bindings.insert(
            statement.symbol_binding.id(),
            IndexedTupleBinding {
                dimension: compiled_body.dimension,
            },
        );

        let target: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_is_tuple: Fact =
            IsTupleFact::new(target.clone(), statement.line_file.clone()).into();
        if is_tuple_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_is_tuple.to_string()
        {
            return Err("indexed tuple first store is not its exact IsTuple fact".into());
        }
        let is_tuple_fact_id = is_tuple_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let is_tuple_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {is_tuple_theorem_name} : {} := by\n  exact ⟨inferInstance⟩",
            render_fact(&expected_is_tuple, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(is_tuple_fact_id, is_tuple_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(is_tuple_fact_id, expected_is_tuple);
        self.next_fact_name_index += 1;

        let expected_dimension: Fact = EqualFact::new(
            TupleDim::new(target.clone()).into(),
            statement.dimension.clone(),
            statement.line_file.clone(),
        )
        .into();
        if dimension_output
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_dimension.to_string()
        {
            return Err("indexed tuple second store is not its exact dimension fact".into());
        }
        let dimension_fact_id = dimension_output
            .fact_id
            .expect("stored tuple output FactId validated above");
        let dimension_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {dimension_theorem_name} : {} := by\n  exact Litex.Same.ofEq (by rfl)",
            render_fact(&expected_dimension, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(dimension_fact_id, dimension_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(dimension_fact_id, expected_dimension);
        self.next_fact_name_index += 1;

        self.compile_indexed_tuple_coordinate_store_result_to_lean_source(
            statement,
            compiled_body.dimension,
            coordinate_output,
        )?;
        Ok(true)
    }

    fn compile_indexed_tuple_coordinate_store_result_to_lean_source(
        &mut self,
        statement: &HaveTupleStmt,
        dimension: usize,
        coordinate_output: &SuccessStoreFactOutput,
    ) -> Result<(), String> {
        let coordinate_fact_id = coordinate_output
            .fact_id
            .ok_or_else(|| "indexed tuple coordinate store has no FactId".to_string())?;
        let Fact::ForallFact(forall) = &coordinate_output.itself_and_why_itself_is_stored.0 else {
            return Err("indexed tuple coordinate store is not a forall fact".into());
        };
        let parameters = forall
            .params_def_with_type
            .collect_param_bindings_with_types();
        let [(binding, param_type)] = parameters.as_slice() else {
            return Err("indexed tuple coordinate store changed its one-index binder".into());
        };
        if !forall.dom_facts.is_empty() || forall.then_facts.len() != 1 {
            return Err(
                "indexed tuple coordinate store changed its domain or conclusion arity".into(),
            );
        }
        let Obj::ClosedRange(range) = parameter_set(param_type)? else {
            return Err("indexed tuple coordinate binder is not a closed range".into());
        };
        let lowered_start = LitexToLeanObjectIr::lower(range.start.as_ref())?;
        let lowered_end = LitexToLeanObjectIr::lower(range.end.as_ref())?;
        if lowered_start
            != (LitexToLeanObjectIr::Number {
                normalized_value: "1".into(),
            })
            || lowered_end != LitexToLeanObjectIr::lower(&statement.dimension)?
        {
            return Err("indexed tuple coordinate range changed its one-based dimension".into());
        }
        let conclusion = forall.then_facts[0].clone().to_fact();
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &conclusion else {
            return Err("indexed tuple coordinate conclusion is not an equality".into());
        };
        let Obj::ObjAtIndex(access) = &equality.left else {
            return Err("indexed tuple coordinate conclusion lost indexed access".into());
        };
        if !object_is_symbol(&access.obj, statement.symbol_binding.id())
            || !object_is_symbol(&access.index, binding.id())
        {
            return Err("indexed tuple coordinate conclusion changed its tuple or index".into());
        }

        let index = "__tuple_index";
        let membership = "__tuple_index_in";
        let exact_index = format!("(Litex.In.rep {index} {membership})");
        let numeric_index = format!("((({exact_index}).val : ℤ) : ℂ)");
        let mut nested = self.environment_stack.clone();
        nested.symbol_names.insert(binding.id(), index.into());
        nested
            .exact_tuple_indices
            .insert(binding.id(), exact_index.clone());
        nested
            .numeric_representations
            .insert(binding.id(), numeric_index.clone());

        let mut source_value_context = self.environment_stack.clone();
        source_value_context
            .symbol_names
            .insert(statement.index_binding.id(), index.into());
        source_value_context
            .numeric_representations
            .insert(statement.index_binding.id(), numeric_index);
        let expected_value = render_numeric_object_ir(
            &LitexToLeanObjectIr::lower(&statement.value)?,
            &source_value_context,
        )?;
        let retained_value =
            render_numeric_object_ir(&LitexToLeanObjectIr::lower(&equality.right)?, &nested)?;
        if retained_value != expected_value {
            return Err("indexed tuple coordinate store changed its value expression".into());
        }

        let rendered_conclusion = render_fact(&conclusion, &nested)?;
        let range = format!("(Litex.closedRange (1 : ℤ) ({dimension} : ℤ))");
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    ∀ {{__tuple_index_carrier : Type}} ({index} : __tuple_index_carrier) ({membership} : Litex.In {index} {range}),\n      {rendered_conclusion} := by\n  intro __tuple_index_carrier {index} {membership}\n  exact Litex.Same.ofEq (by rfl)"
        ));
        self.environment_stack
            .fact_names
            .insert(coordinate_fact_id, theorem_name);
        self.environment_stack.fact_propositions.insert(
            coordinate_fact_id,
            coordinate_output.itself_and_why_itself_is_stored.0.clone(),
        );
        self.next_fact_name_index += 1;
        Ok(())
    }

    /// `Combine`: validate the three named WD children, enter the retained
    /// positive-natural index scope, install its exact parameter FactId,
    /// consume the recursive return-check proof there, and pop the local
    /// compiler environment before publishing the sequence's three outer
    /// facts. No compiler scope is reconstructed from Runtime state.
    fn compile_have_sequence_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveSeqStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if !verification.bound_checks.is_empty() {
            return Err("unbounded sequence retained unexpected bound checks".into());
        }
        let statement = &result.statement;
        let parameter_group = ParamGroupWithSet::new(
            vec![statement.index_binding.clone()],
            StandardSet::NPos.into(),
        );
        let anonymous_function = AnonymousFn::new(
            vec![parameter_group.clone()],
            Vec::new(),
            statement.seq_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LitexToLeanFunctionTypeIr::lower(&function_set)?;
        if function.parameters.len() != 1
            || function.parameters[0].symbol_id != statement.index_binding.id()
            || function.parameters[0].set
                != LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural)
            || !function.domain_facts.is_empty()
            || function.return_set.as_ref()
                != &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
        {
            return Ok(false);
        }

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.seq_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_group.facts_for_binding_scope(ParamObjType::FnSet);
        let [expected_parameter_fact] = expected_parameter_facts.as_slice() else {
            return Err("sequence index scope did not produce one parameter fact".into());
        };
        if !verification.assumption_infers.rule_applications.is_empty() {
            return Err("sequence index assumptions retained unexpected typed infer rules".into());
        }
        let [parameter_store] = verification.assumption_infers.store_fact_outputs.as_slice() else {
            return Err("sequence index scope requires exactly one parameter store".into());
        };
        if parameter_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_parameter_fact.to_string()
        {
            return Err("sequence index scope changed its parameter membership".into());
        }
        let parameter_fact_id = parameter_store
            .fact_id
            .ok_or_else(|| "sequence index parameter store has no FactId".to_string())?;
        if parameter_store.inferred_facts.len() != parameter_store.inferred_fact_ids.len()
            || parameter_store
                .inferred_fact_ids
                .iter()
                .any(Option::is_none)
        {
            return Err("sequence index inference lost an inferred FactId".into());
        }
        let expected_positive_index: Fact = LessFact::new(
            Number::new("0".to_string()).into(),
            obj_for_bound_param_in_scope(&statement.index_binding, ParamObjType::FnSet),
            statement.line_file.clone(),
        )
        .into();
        if parameter_store.inferred_facts.len() != 1
            || parameter_store.inferred_facts[0].to_string() != expected_positive_index.to_string()
        {
            return Err("sequence index scope changed its positive-index inference".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LitexToLeanObjectIr::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.seq_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__arg".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, expected_parameter_fact.clone());
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℂ))".into(),
            );
            self.environment_stack.numeric_real_values.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℝ))".into(),
            );

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "sequence return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err(
                    "sequence return check changed its target or published local effects".into(),
                );
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "sequence return check has no direct recursive Result proof adapter".into(),
                );
            }

            let parameter_real_value = "((((Litex.In.rep __arg __arg_in).val : ℕ) : ℝ))";
            let rendered_body = render_real_function_body(
                &lowered_body,
                statement.index_binding.id(),
                parameter_real_value,
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {rendered_body} }}"
                ),
                parameter_premises: vec![LitexToLeanLocalPremiseIr::new(
                    parameter_fact_id,
                    expected_parameter_fact.clone(),
                )],
                domain_premises: Vec::new(),
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("sequence definition retained unexpected outer typed infer rules".into());
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("sequence definition requires two ordered outer store outputs".into());
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.seq_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("sequence first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "sequence surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err("sequence surface membership must infer one function membership".into());
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("sequence inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("sequence inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err("sequence inferred membership does not retain a function set".into());
        };
        let inferred_function = LitexToLeanFunctionTypeIr::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 1
            || inferred_function.parameters[0].set != compiled_body.function.parameters[0].set
            || !inferred_function.domain_facts.is_empty()
            || inferred_function.return_set != compiled_body.function.return_set
        {
            return Err("sequence inferred function membership changed its signature".into());
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("sequence second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "sequence defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err("sequence outer stores reused a FactId across semantic roles".into());
        }

        let name = lean_identifier(statement.name());
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for sequence `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(&statement.seq_set.clone().into(), &self.environment_stack)?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        // Runtime selects the surface membership FactId as the callable
        // contract. `sequenceSet` is definitionally this exact function set,
        // so preserve that identity instead of substituting the separately
        // inferred function-membership FactId.
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                uses_native_real_body: true,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                compatibility_return_selection: None,
                well_definedness: LitexToLeanWellDefinednessCertificateIr::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: consume the two outer bound checks, validate the three
    /// named WD children, then enter the retained positive-natural parameter
    /// and domain-premise scope. The local parameter/domain FactIds are
    /// available while compiling the recursive return check and disappear
    /// when that Result field closes. Only then are the three persistent
    /// definition facts published in the parent compiler environment.
    fn compile_have_finite_sequence_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFiniteSeqStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let [positive_bound_check, matching_length_check] = verification.bound_checks.as_slice()
        else {
            return Err("finite-sequence verification requires two ordered bound checks".into());
        };
        let expected_positive_bound: Fact = InFact::new(
            statement.bound.clone(),
            StandardSet::NPos.into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_matching_length: Fact = EqualFact::new(
            statement.bound.clone(),
            statement.finite_seq_set.n.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        for (label, checked_result, expected_fact) in [
            (
                "positive bound",
                positive_bound_check,
                &expected_positive_bound,
            ),
            (
                "matching length",
                matching_length_check,
                &expected_matching_length,
            ),
        ] {
            let checked_fact = checked_result
                .factual_success()
                .ok_or_else(|| format!("finite-sequence {label} check is not factual"))?;
            if checked_fact.fact().to_string() != expected_fact.to_string()
                || checked_fact.store.fact.to_string() != expected_fact.to_string()
                || !checked_fact.store.infers.is_empty()
            {
                return Err(format!(
                    "finite-sequence {label} check changed its target or published effects"
                ));
            }
            if self
                .construct_lean_proof_from_direct_fact_result(checked_fact)?
                .is_none()
            {
                return Err(format!(
                    "finite-sequence {label} check has no direct recursive Result proof adapter"
                ));
            }
        }

        let index_object =
            obj_for_bound_param_in_scope(&statement.index_binding, ParamObjType::FnSet);
        let expected_domain_atomic_fact: AtomicFact = LessEqualFact::new(
            index_object,
            statement.bound.clone(),
            statement.line_file.clone(),
        )
        .into();
        let expected_domain_fact: Fact = expected_domain_atomic_fact.clone().into();
        let parameter_group = ParamGroupWithSet::new(
            vec![statement.index_binding.clone()],
            StandardSet::NPos.into(),
        );
        let anonymous_function = AnonymousFn::new(
            vec![parameter_group.clone()],
            vec![expected_domain_atomic_fact.into()],
            statement.finite_seq_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LitexToLeanFunctionTypeIr::lower(&function_set)?;
        if function.parameters.len() != 1
            || function.parameters[0].symbol_id != statement.index_binding.id()
            || function.parameters[0].set
                != LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural)
            || function.domain_facts.len() != 1
            || function.return_set.as_ref()
                != &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
            || !function_uses_telescope(&function)
        {
            return Ok(false);
        }
        // The target `finiteSequenceSet` ABI currently requires a closed
        // natural length. Validate this support boundary before mutating any
        // compiler environment.
        let lowered_length = LitexToLeanObjectIr::lower(statement.finite_seq_set.n.as_ref())?;
        render_natural_endpoint(&lowered_length)?;

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.finite_seq_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_group.facts_for_binding_scope(ParamObjType::FnSet);
        let [expected_parameter_fact] = expected_parameter_facts.as_slice() else {
            return Err("finite-sequence index scope did not produce one parameter fact".into());
        };
        if !verification.assumption_infers.rule_applications.is_empty() {
            return Err(
                "finite-sequence index assumptions retained unexpected typed infer rules".into(),
            );
        }
        let [parameter_store, domain_store] =
            verification.assumption_infers.store_fact_outputs.as_slice()
        else {
            return Err(
                "finite-sequence index scope requires one parameter store and one domain store"
                    .into(),
            );
        };
        if parameter_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_parameter_fact.to_string()
        {
            return Err("finite-sequence index scope changed its parameter membership".into());
        }
        let parameter_fact_id = parameter_store
            .fact_id
            .ok_or_else(|| "finite-sequence index parameter store has no FactId".to_string())?;
        if parameter_store.inferred_facts.len() != parameter_store.inferred_fact_ids.len()
            || parameter_store
                .inferred_fact_ids
                .iter()
                .any(Option::is_none)
        {
            return Err("finite-sequence index inference lost an inferred FactId".into());
        }
        let expected_positive_index: Fact = LessFact::new(
            Number::new("0".to_string()).into(),
            obj_for_bound_param_in_scope(&statement.index_binding, ParamObjType::FnSet),
            statement.line_file.clone(),
        )
        .into();
        if parameter_store.inferred_facts.len() != 1
            || parameter_store.inferred_facts[0].to_string() != expected_positive_index.to_string()
        {
            return Err("finite-sequence index scope changed its positive-index inference".into());
        }
        if domain_store.itself_and_why_itself_is_stored.0.to_string()
            != expected_domain_fact.to_string()
            || !domain_store.inferred_facts.is_empty()
            || !domain_store.inferred_fact_ids.is_empty()
        {
            return Err("finite-sequence index scope changed its domain premise".into());
        }
        let domain_fact_id = domain_store
            .fact_id
            .ok_or_else(|| "finite-sequence domain store has no FactId".to_string())?;
        if parameter_fact_id == domain_fact_id {
            return Err("finite-sequence local parameter and domain stores reused a FactId".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LitexToLeanObjectIr::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.finite_seq_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            self.environment_stack
                .symbol_names
                .insert(statement.index_binding.id(), "__arg1".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg1_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, expected_parameter_fact.clone());
            self.environment_stack
                .fact_names
                .insert(domain_fact_id, "__arg_domain".into());
            self.environment_stack
                .fact_propositions
                .insert(domain_fact_id, expected_domain_fact.clone());
            self.environment_stack.numeric_representations.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℂ))".into(),
            );
            self.environment_stack.numeric_real_values.insert(
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℝ))".into(),
            );

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "finite-sequence return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err(
                    "finite-sequence return check changed its target or published local effects"
                        .into(),
                );
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "finite-sequence return check has no direct recursive Result proof adapter"
                        .into(),
                );
            }

            let rendered_body = render_real_function_body(
                &lowered_body,
                statement.index_binding.id(),
                "((((Litex.In.rep __arg1 __arg1_in).val : ℕ) : ℝ))",
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "fun {{__alpha1 : Type}} (__arg1 : __alpha1) (__arg1_in : Litex.In __arg1 Litex.NPos) => fun __arg_domain => ULift.up ({rendered_body})"
                ),
                parameter_premises: vec![LitexToLeanLocalPremiseIr::new(
                    parameter_fact_id,
                    expected_parameter_fact.clone(),
                )],
                domain_premises: vec![LitexToLeanLocalPremiseIr::new(
                    domain_fact_id,
                    expected_domain_fact.clone(),
                )],
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err(
                "finite-sequence definition retained unexpected outer typed infer rules".into(),
            );
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err(
                "finite-sequence definition requires two ordered outer store outputs".into(),
            );
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.finite_seq_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("finite-sequence first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "finite-sequence surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err(
                "finite-sequence surface membership must infer one function membership".into(),
            );
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("finite-sequence inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("finite-sequence inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err(
                "finite-sequence inferred membership does not retain a function set".into(),
            );
        };
        let inferred_function = LitexToLeanFunctionTypeIr::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 1
            || inferred_function.parameters[0].set != compiled_body.function.parameters[0].set
            || inferred_function.domain_facts.len() != 1
            || inferred_function.return_set != compiled_body.function.return_set
        {
            return Err(
                "finite-sequence inferred function membership changed its signature".into(),
            );
        }
        let mut expected_domain_environment = self.environment_stack.clone();
        expected_domain_environment.symbol_names.insert(
            compiled_body.function.parameters[0].symbol_id,
            "__finite_sequence_index".into(),
        );
        expected_domain_environment.numeric_representations.insert(
            compiled_body.function.parameters[0].symbol_id,
            "__finite_sequence_index_complex".into(),
        );
        let mut inferred_domain_environment = self.environment_stack.clone();
        inferred_domain_environment.symbol_names.insert(
            inferred_function.parameters[0].symbol_id,
            "__finite_sequence_index".into(),
        );
        inferred_domain_environment.numeric_representations.insert(
            inferred_function.parameters[0].symbol_id,
            "__finite_sequence_index_complex".into(),
        );
        if render_fact(
            &compiled_body.function.domain_facts[0],
            &expected_domain_environment,
        )? != render_fact(
            &inferred_function.domain_facts[0],
            &inferred_domain_environment,
        )? {
            return Err(
                "finite-sequence inferred function membership changed its bound clause".into(),
            );
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("finite-sequence second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "finite-sequence defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err(
                "finite-sequence outer stores reused a FactId across semantic roles".into(),
            );
        }

        let name = lean_identifier(statement.name());
        let function_value_name = format!("(@{name})");
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for finite sequence `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {function_value_name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(
                &statement.finite_seq_set.clone().into(),
                &self.environment_stack,
            )?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {function_value_name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {function_value_name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                uses_native_real_body: true,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                compatibility_return_selection: None,
                well_definedness: LitexToLeanWellDefinednessCertificateIr::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: consume four outer row/column bound checks, enter one local
    /// Result layer containing two parameter stores, two domain-premise
    /// stores, and the recursive return check, then publish only the matrix's
    /// persistent facts after that compiler environment has been popped.
    fn compile_have_matrix_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveMatrixStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let statement = &result.statement;
        let expected_bound_checks: [Fact; 4] = [
            InFact::new(
                statement.row_bound.clone(),
                StandardSet::NPos.into(),
                statement.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                statement.row_bound.clone(),
                statement.matrix_set.row_len.as_ref().clone(),
                statement.line_file.clone(),
            )
            .into(),
            InFact::new(
                statement.col_bound.clone(),
                StandardSet::NPos.into(),
                statement.line_file.clone(),
            )
            .into(),
            EqualFact::new(
                statement.col_bound.clone(),
                statement.matrix_set.col_len.as_ref().clone(),
                statement.line_file.clone(),
            )
            .into(),
        ];
        if verification.bound_checks.len() != expected_bound_checks.len() {
            return Err("matrix verification requires four ordered bound checks".into());
        }
        for (check_index, (checked_result, expected_fact)) in verification
            .bound_checks
            .iter()
            .zip(expected_bound_checks.iter())
            .enumerate()
        {
            let checked_fact = checked_result
                .factual_success()
                .ok_or_else(|| format!("matrix bound check {check_index} is not factual"))?;
            if checked_fact.fact().to_string() != expected_fact.to_string()
                || checked_fact.store.fact.to_string() != expected_fact.to_string()
                || !checked_fact.store.infers.is_empty()
            {
                return Err(format!(
                    "matrix bound check {check_index} changed its target or published effects"
                ));
            }
            if self
                .construct_lean_proof_from_direct_fact_result(checked_fact)?
                .is_none()
            {
                return Err(format!(
                    "matrix bound check {check_index} has no direct recursive Result proof adapter"
                ));
            }
        }

        let parameter_groups = [
            ParamGroupWithSet::new(
                vec![statement.row_index_binding.clone()],
                StandardSet::NPos.into(),
            ),
            ParamGroupWithSet::new(
                vec![statement.col_index_binding.clone()],
                StandardSet::NPos.into(),
            ),
        ];
        let domain_atomic_facts = [
            AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&statement.row_index_binding, ParamObjType::FnSet),
                statement.row_bound.clone(),
                statement.line_file.clone(),
            )),
            AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&statement.col_index_binding, ParamObjType::FnSet),
                statement.col_bound.clone(),
                statement.line_file.clone(),
            )),
        ];
        let expected_domain_facts = domain_atomic_facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let anonymous_function = AnonymousFn::new(
            parameter_groups.to_vec(),
            domain_atomic_facts
                .iter()
                .cloned()
                .map(QuantifierFreeFact::from)
                .collect(),
            statement.matrix_set.set.as_ref().clone(),
            statement.value.clone(),
        )
        .map_err(|error| error.to_string())?;
        let function_set =
            FnSet::from_body(anonymous_function.body.clone()).map_err(|error| error.to_string())?;
        let function = LitexToLeanFunctionTypeIr::lower(&function_set)?;
        if function.parameters.len() != 2
            || function.parameters[0].symbol_id != statement.row_index_binding.id()
            || function.parameters[1].symbol_id != statement.col_index_binding.id()
            || function.parameters.iter().any(|parameter| {
                parameter.set
                    != LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural)
            })
            || function.domain_facts.len() != 2
            || function.return_set.as_ref()
                != &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
            || !function_uses_telescope(&function)
        {
            return Ok(false);
        }
        for count in [
            statement.matrix_set.row_len.as_ref(),
            statement.matrix_set.col_len.as_ref(),
        ] {
            render_natural_endpoint(&LitexToLeanObjectIr::lower(count)?)?;
        }

        let mut visited_well_definedness_results = HashSet::new();
        validate_success_obj_well_defined_result(
            verification.well_definedness.surface_set.as_ref(),
            &statement.matrix_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.anonymous_function.as_ref(),
            &anonymous_function.clone().into(),
            &mut visited_well_definedness_results,
        )?;
        validate_success_obj_well_defined_result(
            verification.well_definedness.function_set.as_ref(),
            &function_set.clone().into(),
            &mut visited_well_definedness_results,
        )?;

        let expected_parameter_facts = parameter_groups
            .iter()
            .flat_map(|group| group.facts_for_binding_scope(ParamObjType::FnSet))
            .collect::<Vec<_>>();
        if expected_parameter_facts.len() != 2 {
            return Err("matrix index scope did not produce two parameter facts".into());
        }
        if !verification.assumption_infers.rule_applications.is_empty() {
            return Err("matrix index assumptions retained unexpected typed infer rules".into());
        }
        let assumption_stores = &verification.assumption_infers.store_fact_outputs;
        if assumption_stores.len() != 4 {
            return Err(
                "matrix index scope requires two parameter stores and two domain stores".into(),
            );
        }
        let mut parameter_fact_ids = Vec::with_capacity(2);
        let parameter_bindings = [&statement.row_index_binding, &statement.col_index_binding];
        for parameter_index in 0..2 {
            let store = &assumption_stores[parameter_index];
            let expected_fact = &expected_parameter_facts[parameter_index];
            if store.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string() {
                return Err(format!(
                    "matrix parameter store {parameter_index} changed its membership"
                ));
            }
            let fact_id = store
                .fact_id
                .ok_or_else(|| format!("matrix parameter store {parameter_index} has no FactId"))?;
            let expected_positive: Fact = LessFact::new(
                Number::new("0".to_string()).into(),
                obj_for_bound_param_in_scope(
                    parameter_bindings[parameter_index],
                    ParamObjType::FnSet,
                ),
                statement.line_file.clone(),
            )
            .into();
            if store.inferred_facts.len() != 1
                || store.inferred_fact_ids.len() != 1
                || store.inferred_fact_ids[0].is_none()
                || store.inferred_facts[0].to_string() != expected_positive.to_string()
            {
                return Err(format!(
                    "matrix parameter store {parameter_index} changed its positive-index inference"
                ));
            }
            parameter_fact_ids.push(fact_id);
        }
        let mut domain_fact_ids = Vec::with_capacity(2);
        for domain_index in 0..2 {
            let store = &assumption_stores[domain_index + 2];
            if store.itself_and_why_itself_is_stored.0.to_string()
                != expected_domain_facts[domain_index].to_string()
                || !store.inferred_facts.is_empty()
                || !store.inferred_fact_ids.is_empty()
            {
                return Err(format!(
                    "matrix domain store {domain_index} changed its premise"
                ));
            }
            domain_fact_ids.push(
                store
                    .fact_id
                    .ok_or_else(|| format!("matrix domain store {domain_index} has no FactId"))?,
            );
        }
        if parameter_fact_ids
            .iter()
            .chain(domain_fact_ids.iter())
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != 4
        {
            return Err("matrix local stores reused a FactId across semantic roles".into());
        }

        let source_body = statement.value.clone();
        let lowered_body = LitexToLeanObjectIr::lower(&source_body)?;
        let expected_return_check: Fact = InFact::new(
            source_body.clone(),
            statement.matrix_set.set.as_ref().clone(),
            statement.line_file.clone(),
        )
        .into();
        self.environment_stack.push_inherited_environment();
        let compiled_body: Result<CompiledIndexedFunctionDefinitionBody, String> = (|| {
            let mut parameter_premises = Vec::with_capacity(2);
            let mut parameter_real_representations = HashMap::new();
            for parameter_index in 0..2 {
                let suffix = parameter_index + 1;
                let argument_name = format!("__arg{suffix}");
                let membership_name = format!("__arg{suffix}_in");
                let binding = parameter_bindings[parameter_index];
                let fact_id = parameter_fact_ids[parameter_index];
                self.environment_stack
                    .symbol_names
                    .insert(binding.id(), argument_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(fact_id, membership_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, expected_parameter_facts[parameter_index].clone());
                let representative = format!("Litex.In.rep {argument_name} {membership_name}");
                let numeric_complex = format!("((((({representative}).val : ℕ)) : ℂ))");
                let numeric_real = format!("((((({representative}).val : ℕ)) : ℝ))");
                self.environment_stack
                    .numeric_representations
                    .insert(binding.id(), numeric_complex);
                self.environment_stack
                    .numeric_real_values
                    .insert(binding.id(), numeric_real.clone());
                parameter_real_representations.insert(binding.id(), numeric_real);
                parameter_premises.push(LitexToLeanLocalPremiseIr::new(
                    fact_id,
                    expected_parameter_facts[parameter_index].clone(),
                ));
            }
            let mut domain_premises = Vec::with_capacity(2);
            for domain_index in 0..2 {
                let fact_id = domain_fact_ids[domain_index];
                let proof_name = if domain_index == 0 {
                    "__arg_domain.1"
                } else {
                    "__arg_domain.2"
                };
                self.environment_stack
                    .fact_names
                    .insert(fact_id, proof_name.into());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, expected_domain_facts[domain_index].clone());
                domain_premises.push(LitexToLeanLocalPremiseIr::new(
                    fact_id,
                    expected_domain_facts[domain_index].clone(),
                ));
            }

            let mut installed_well_definedness_nodes = HashSet::new();
            for well_definedness in [
                verification.well_definedness.surface_set.as_ref(),
                verification.well_definedness.anonymous_function.as_ref(),
                verification.well_definedness.function_set.as_ref(),
            ] {
                install_object_well_definedness_store_results(
                    well_definedness,
                    &mut self.environment_stack,
                    &mut installed_well_definedness_nodes,
                )?;
            }

            let return_check = verification
                .return_check
                .factual_success()
                .ok_or_else(|| "matrix return check is not factual".to_string())?;
            if return_check.fact().to_string() != expected_return_check.to_string()
                || return_check.store.fact.to_string() != expected_return_check.to_string()
                || !return_check.store.infers.is_empty()
            {
                return Err("matrix return check changed its target or published effects".into());
            }
            if self
                .construct_lean_proof_from_direct_fact_result(return_check)?
                .is_none()
            {
                return Err(
                    "matrix return check has no direct recursive Result proof adapter".into(),
                );
            }
            let rendered_body = render_real_function_body_with_parameters(
                &lowered_body,
                &parameter_real_representations,
                &self.environment_stack,
            )?;
            Ok(CompiledIndexedFunctionDefinitionBody {
                function: function.clone(),
                source_body: source_body.clone(),
                lowered_body: lowered_body.clone(),
                value: format!(
                    "fun {{__alpha1 : Type}} (__arg1 : __alpha1) (__arg1_in : Litex.In __arg1 Litex.NPos) => fun {{__alpha2 : Type}} (__arg2 : __alpha2) (__arg2_in : Litex.In __arg2 Litex.NPos) => fun __arg_domain => ULift.up ({rendered_body})"
                ),
                parameter_premises,
                domain_premises,
            })
        })();
        self.environment_stack.pop_local_environment();
        let compiled_body = compiled_body?;

        if !result.common.infers.rule_applications.is_empty() {
            return Err("matrix definition retained unexpected outer typed infer rules".into());
        }
        let [surface_membership_store, defining_equality_store] =
            result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err("matrix definition requires two ordered outer store outputs".into());
        };
        let function_object: Obj = Identifier::new_bound(
            statement.name().to_string(),
            statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_surface_membership: Fact = InFact::new(
            function_object.clone(),
            statement.matrix_set.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        let expected_defining_equality: Fact = EqualFact::new(
            function_object.clone(),
            anonymous_function.clone().into(),
            statement.line_file.clone(),
        )
        .into();
        if surface_membership_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_surface_membership.to_string()
        {
            return Err("matrix first outer store changed its surface membership".into());
        }
        let surface_membership_fact_id = surface_membership_store
            .fact_id
            .ok_or_else(|| "matrix surface membership store has no FactId".to_string())?;
        let [inferred_function_membership] = surface_membership_store.inferred_facts.as_slice()
        else {
            return Err("matrix surface membership must infer one function membership".into());
        };
        let [Some(function_membership_fact_id)] =
            surface_membership_store.inferred_fact_ids.as_slice()
        else {
            return Err("matrix inferred function membership has no FactId".into());
        };
        let (inferred_function_object, inferred_function_set) =
            membership_parts(inferred_function_membership)?;
        if !object_is_symbol(inferred_function_object, statement.symbol_binding.id()) {
            return Err("matrix inferred function membership changed its function".into());
        }
        let Obj::FnSet(inferred_function_set) = inferred_function_set else {
            return Err("matrix inferred membership does not retain a function set".into());
        };
        let inferred_function = LitexToLeanFunctionTypeIr::lower(inferred_function_set)?;
        if inferred_function.parameters.len() != 2
            || inferred_function.domain_facts.len() != 2
            || inferred_function.return_set != compiled_body.function.return_set
            || inferred_function
                .parameters
                .iter()
                .zip(compiled_body.function.parameters.iter())
                .any(|(inferred, expected)| inferred.set != expected.set)
        {
            return Err("matrix inferred function membership changed its signature".into());
        }
        let mut expected_domain_environment = self.environment_stack.clone();
        let mut inferred_domain_environment = self.environment_stack.clone();
        for parameter_index in 0..2 {
            let common_name = format!("__matrix_parameter{}", parameter_index + 1);
            let common_numeric = format!("__matrix_parameter{}_complex", parameter_index + 1);
            expected_domain_environment.symbol_names.insert(
                compiled_body.function.parameters[parameter_index].symbol_id,
                common_name.clone(),
            );
            expected_domain_environment.numeric_representations.insert(
                compiled_body.function.parameters[parameter_index].symbol_id,
                common_numeric.clone(),
            );
            inferred_domain_environment.symbol_names.insert(
                inferred_function.parameters[parameter_index].symbol_id,
                common_name,
            );
            inferred_domain_environment.numeric_representations.insert(
                inferred_function.parameters[parameter_index].symbol_id,
                common_numeric,
            );
        }
        for domain_index in 0..2 {
            if render_fact(
                &compiled_body.function.domain_facts[domain_index],
                &expected_domain_environment,
            )? != render_fact(
                &inferred_function.domain_facts[domain_index],
                &inferred_domain_environment,
            )? {
                return Err(format!(
                    "matrix inferred function membership changed bound clause {domain_index}"
                ));
            }
        }
        if defining_equality_store
            .itself_and_why_itself_is_stored
            .0
            .to_string()
            != expected_defining_equality.to_string()
            || !defining_equality_store.inferred_facts.is_empty()
            || !defining_equality_store.inferred_fact_ids.is_empty()
        {
            return Err("matrix second outer store changed its defining equality".into());
        }
        let defining_equality_fact_id = defining_equality_store
            .fact_id
            .ok_or_else(|| "matrix defining equality store has no FactId".to_string())?;
        if [
            surface_membership_fact_id,
            *function_membership_fact_id,
            defining_equality_fact_id,
        ]
        .into_iter()
        .collect::<HashSet<_>>()
        .len()
            != 3
        {
            return Err("matrix outer stores reused a FactId across semantic roles".into());
        }

        let name = lean_identifier(statement.name());
        let function_value_name = format!("(@{name})");
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), function_value_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for matrix `{}`",
                statement.name()
            ));
        }
        let function_type = render_function_type(&compiled_body.function, &self.environment_stack)?;
        let rendered_function_set =
            render_function_set(&compiled_body.function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {}",
            compiled_body.value
        ));

        let surface_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {surface_theorem_name} : {} := by\n  exact Litex.In.own {} {function_value_name}",
            render_fact(&expected_surface_membership, &self.environment_stack)?,
            render_obj(&statement.matrix_set.clone().into(), &self.environment_stack)?,
        ));
        self.environment_stack
            .fact_names
            .insert(surface_membership_fact_id, surface_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(surface_membership_fact_id, expected_surface_membership);
        self.environment_stack.function_bindings.insert(
            surface_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: surface_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let function_membership_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {function_membership_theorem_name} : {} := by\n  exact Litex.In.own {rendered_function_set} {function_value_name}",
            render_fact(inferred_function_membership, &self.environment_stack)?,
        ));
        self.environment_stack.fact_names.insert(
            *function_membership_fact_id,
            function_membership_theorem_name.clone(),
        );
        self.environment_stack.fact_propositions.insert(
            *function_membership_fact_id,
            inferred_function_membership.clone(),
        );
        self.environment_stack.function_bindings.insert(
            *function_membership_fact_id,
            FunctionBinding {
                symbol_id: statement.symbol_binding.id(),
                function: compiled_body.function.clone(),
                membership_proof_name: function_membership_theorem_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {equality_theorem_name} : Litex.Same {function_value_name} ({} : {function_type}) := by\n  unfold {name}\n  exact Litex.Same.refl ({} : {function_type})",
            compiled_body.value, compiled_body.value
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, equality_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, expected_defining_equality);
        self.environment_stack.named_function_definitions.insert(
            defining_equality_fact_id,
            NamedFunctionDefinitionBinding {
                symbol_id: statement.symbol_binding.id(),
                name,
                function: compiled_body.function,
                source_body: compiled_body.source_body,
                body: compiled_body.lowered_body,
                uses_native_real_body: true,
                parameter_premises: compiled_body.parameter_premises,
                domain_premises: compiled_body.domain_premises,
                compatibility_return_selection: None,
                well_definedness: LitexToLeanWellDefinednessCertificateIr::default(),
            },
        );
        self.next_fact_name_index += 1;
        Ok(true)
    }

    fn compile_def_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("concrete predicate definition unexpectedly retained fact effects".into());
        }
        let definition = &result.statement;
        if definition.iff_facts.is_empty() {
            return Err("compiler rejects a bodyless concrete `prop`".into());
        }
        if self
            .environment_stack
            .predicate_bindings
            .contains_key(&definition.name)
        {
            return Err(format!(
                "duplicate compiler predicate definition `{}`",
                definition.name
            ));
        }

        let mut definition_environment = self.environment_stack.clone();
        definition_environment.push_inherited_environment();
        let mut binders = Vec::new();
        let mut requirements = Vec::new();
        let mut parameter_count = 0;
        for group in &definition.params_def_with_type.groups {
            let set = parameter_set(&group.param_type)?;
            for binding in &group.params {
                parameter_count += 1;
                let parameter_name = lean_identifier(binding.name());
                let carrier_name = format!("__carrier{parameter_count}");
                let rendered_set = render_obj(set, &definition_environment)?;
                binders.push(format!("{{{carrier_name} : Type}}"));
                binders.push(format!("({parameter_name} : {carrier_name})"));
                definition_environment
                    .symbol_names
                    .insert(binding.id(), parameter_name.clone());
                requirements.push(format!("Litex.In {parameter_name} {rendered_set}"));
            }
        }
        let clauses = definition
            .iff_facts
            .iter()
            .map(|fact| render_fact(fact, &definition_environment))
            .collect::<Result<Vec<_>, _>>()?;
        let mut components = requirements;
        components.extend(clauses);
        let lean_name = lean_identifier(&definition.name);
        self.declarations.push(format!(
            "def {lean_name} {} : Prop :=\n  {}",
            binders.join(" "),
            conjunction(&components)
        ));
        self.environment_stack.predicate_bindings.insert(
            definition.name.clone(),
            PredicateBinding {
                lean_name,
                parameter_count,
                requirement_count: parameter_count,
                clause_count: definition.iff_facts.len(),
                definition: Some(definition.clone()),
            },
        );
        Ok(())
    }

    fn compile_def_abstract_prop_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefAbstractPropStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("abstract predicate definition unexpectedly retained fact effects".into());
        }
        construct_lean_source_parts_for_abstract_predicate_definition(
            &result.statement.name,
            &result.statement.params,
            &mut self.declarations,
            &mut self.environment_stack,
        )
    }

    fn compile_by_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_definition_stmt_result(result)? else {
            return Ok(false);
        };
        if !result.common.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        if result.common.infers.store_fact_outputs.is_empty() {
            let target_was_already_visible = self
                .environment_stack
                .fact_propositions
                .values()
                .any(|visible| visible.to_string() == proof.target.fact.to_string());
            if !target_was_already_visible {
                return Err(
                    "by-definition target was neither stored nor already compiler-visible".into(),
                );
            }
            return Ok(true);
        }
        let [output] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("by-definition target retained more than one direct store output".into());
        };
        if output.itself_and_why_itself_is_stored.0.to_string() != proof.target.fact.to_string()
            || output.inferred_facts.len() != output.inferred_fact_ids.len()
        {
            return Err("by-definition target changed its direct or inferred effects".into());
        }
        let fact_id = output
            .fact_id
            .ok_or_else(|| "by-definition target store has no FactId".to_string())?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof.target.proposition, proof.target.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.target.fact);
        self.next_fact_name_index += 1;

        for (inferred_fact, inferred_fact_id) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
        {
            let inferred_fact_id = inferred_fact_id.ok_or_else(|| {
                format!("by-definition inferred fact `{inferred_fact}` has no retained FactId")
            })?;
            if self
                .environment_stack
                .fact_propositions
                .contains_key(&inferred_fact_id)
            {
                resolve_fact_citation(&inferred_fact_id, inferred_fact, &self.environment_stack)?;
                continue;
            }
            let component = proof
                .components
                .iter()
                .find(|component| {
                    component.retained_fact_id == Some(inferred_fact_id)
                        && component.fact.to_string() == inferred_fact.to_string()
                })
                .ok_or_else(|| {
                    format!(
                        "by-definition inferred fact `{inferred_fact}` has no matching recursive child proof"
                    )
                })?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := by\n  exact {}",
                component.proposition, component.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(inferred_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(inferred_fact_id, component.fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: validate each parameter and definition-clause child in
    /// source order, then fold those exact proofs into the predicate.
    fn construct_lean_proof_from_by_definition_stmt_result(
        &mut self,
        result: &SuccessByDefStmtResult,
    ) -> Result<Option<CompiledByDefinitionProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if !verification.concrete_user_prop {
            return Ok(None);
        }
        let Some(definition) = &verification.definition else {
            return Err("by-definition Result lost its concrete predicate definition".into());
        };
        if definition.iff_facts.is_empty() {
            return Err("by-definition Result retained a bodyless concrete predicate".into());
        }
        let target: Fact = result.statement.fact.clone().into();
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)) = &target else {
            return Err("concrete by-definition target is not a predicate application".into());
        };
        if verification.prop != target_predicate.predicate.to_string()
            || verification.stored_fact != target.to_string()
            || verification.arguments
                != target_predicate
                    .body
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            || verification.definition_clauses
                != verification
                    .definition_clause_facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("by-definition Result changed its target, arguments, or clauses".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "by-definition references unavailable predicate `{}`",
                    definition.name
                )
            })?;
        let Some(active_definition) = &binding.definition else {
            return Err("by-definition selected an abstract predicate binding".into());
        };
        if active_definition.to_string() != definition.to_string()
            || target_predicate.predicate.to_string() != definition.name
        {
            return Err(
                "by-definition Result does not match the active predicate definition".into(),
            );
        }
        let Some(argument_verification) = &verification.argument_verification else {
            return Err("by-definition Result has no parameter-check children".into());
        };
        if !argument_verification.infers.is_empty() {
            return Ok(None);
        }
        if argument_verification.checks.len() != binding.requirement_count
            || verification.definition_clause_facts.len() != binding.clause_count
            || verification.clause_checks.len() != binding.clause_count
        {
            return Err("by-definition Result changed its component arity".into());
        }

        let expected_components =
            instantiated_predicate_components(&target, &binding, &self.environment_stack)?;
        if expected_components.len() != binding.requirement_count + binding.clause_count {
            return Err("active predicate definition produced an invalid component arity".into());
        }
        let mut components = Vec::with_capacity(expected_components.len());
        for (component_index, check) in argument_verification.checks.iter().enumerate() {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition parameter child is not factual".to_string())?;
            validate_scoped_fact_check_result(
                check,
                &check.fact(),
                &format!("by-definition parameter check {component_index}"),
            )?;
            if render_fact(&check.fact(), &self.environment_stack)?
                != expected_components[component_index]
            {
                return Err(format!(
                    "by-definition parameter check {component_index} changed its expected fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Ok(None);
            };
            components.push(CompiledByDefinitionComponentProofBody {
                fact: check.fact(),
                retained_fact_id: check.store.fact_id,
                proposition: expected_components[component_index].clone(),
                proof_expression: proof,
            });
        }
        for (clause_index, (retained_clause, check)) in verification
            .definition_clause_facts
            .iter()
            .zip(verification.clause_checks.iter())
            .enumerate()
        {
            let check = check
                .factual_success()
                .ok_or_else(|| "by-definition clause child is not factual".to_string())?;
            if check.fact().to_string() != retained_clause.to_string() {
                return Err(format!(
                    "by-definition clause check {clause_index} changed its retained fact"
                ));
            }
            validate_scoped_fact_check_result(
                check,
                retained_clause,
                &format!("by-definition clause check {clause_index}"),
            )?;
            let component_index = binding.requirement_count + clause_index;
            if render_fact(retained_clause, &self.environment_stack)?
                != expected_components[component_index]
            {
                return Err(format!(
                    "by-definition clause check {clause_index} changed its expected fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Ok(None);
            };
            components.push(CompiledByDefinitionComponentProofBody {
                fact: retained_clause.clone(),
                retained_fact_id: check.store.fact_id,
                proposition: expected_components[component_index].clone(),
                proof_expression: proof,
            });
        }
        if components.is_empty() {
            return Err("by-definition Result retained no proof components".into());
        }
        let target_proof_expression = format!(
            "(by\n  unfold {}\n  exact ⟨{}⟩)",
            binding.lean_name,
            components
                .iter()
                .map(|component| component.proof_expression.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        Ok(Some(CompiledByDefinitionProofBody {
            target: CompiledFactProofBody {
                fact: target.clone(),
                proposition: render_fact(&target, &self.environment_stack)?,
                proof_expression: target_proof_expression,
            },
            components,
        }))
    }

    fn compile_trust_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTrustStmtResult,
    ) -> Result<bool, String> {
        if result.statement.facts.is_empty() {
            return Err("explicit source `trust` retained no propositions".into());
        }
        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.len() != result.statement.facts.len()
            || result.common.infers.store_fact_outputs.iter().any(|store| {
                !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty()
            })
        {
            return Ok(false);
        }
        for (fact, store) in result
            .statement
            .facts
            .iter()
            .zip(result.common.infers.store_fact_outputs.iter())
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != fact.to_string() {
                return Err("trusted fact order changed between statement and store Result".into());
            }
            let fact_id = store
                .fact_id
                .ok_or_else(|| "trusted source fact has no FactId".to_string())?;
            let proposition = match fact {
                Fact::ForallFact(forall) => {
                    render_forall_fact_type(forall, &self.environment_stack)?
                }
                _ => render_fact(fact, &self.environment_stack)?,
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations
                .push(format!("axiom {theorem_name} : {proposition}"));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    fn compile_let_obj_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessLetObjStmtResult,
    ) -> Result<(), String> {
        let statement = &result.statement;
        let source_name = statement.symbol_binding.name();
        let lean_name = lean_identifier(source_name);
        let rendered_value = render_obj(&statement.value, &self.environment_stack)?;
        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{source_name}`"
            ));
        }
        self.declarations
            .push(format!("noncomputable def {lean_name} := {rendered_value}"));

        if !result.common.infers.rule_applications.is_empty() {
            return Err("let-object definition retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("let-object definition must retain exactly one defining store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("let-object defining store retained unexpected inferred facts".into());
        }
        let defined_object: Obj =
            Identifier::new_bound(source_name.to_string(), statement.symbol_binding.as_ref())
                .into();
        let defining_equality: Fact = EqualFact::new(
            defined_object,
            statement.value.clone(),
            statement.line_file.clone(),
        )
        .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != defining_equality.to_string() {
            return Err("let-object result changed its defining equality".into());
        }
        let defining_equality_fact_id = store
            .fact_id
            .ok_or_else(|| "let-object defining equality has no FactId".to_string())?;
        let rendered_equality = render_fact(&defining_equality, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
        ));
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, defining_equality);
        self.next_fact_name_index += 1;
        Ok(())
    }

    fn compile_try_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTryStmtResult,
    ) -> Result<(), String> {
        let proof = result
            .proof
            .as_ref()
            .ok_or_else(|| "successful `try` retained no child results".to_string())?;
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("successful `try` changed its source statement order".into());
        }
        for child in &proof.proof_steps {
            self.compile_stmt_result_to_lean_source(child)?;
        }
        Ok(())
    }

    fn compile_do_nothing_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDoNothingStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("`do_nothing` unexpectedly changed the compiler environment".into());
        }
        Ok(())
    }

    /// `Combine`: compile the witness's local proof-step Results, its checked
    /// parameter requirement, and its checked body fact before publishing the
    /// introduced existential under the exact outer store FactId.
    fn compile_witness_exist_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessWitnessExistFactResult,
    ) -> Result<bool, String> {
        let Some(proof_body) =
            self.construct_lean_proof_from_witness_exist_fact_stmt_result(result)?
        else {
            return Ok(false);
        };
        let existential: Fact = result.statement.exist_fact_in_witness.clone().into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &existential,
            "existential witness outer effect",
        )?;

        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof_body.proposition, proof_body.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, existential);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    fn construct_lean_proof_from_witness_exist_fact_stmt_result(
        &mut self,
        result: &SuccessWitnessExistFactResult,
    ) -> Result<Option<CompiledExistentialWitnessProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let statement = &result.statement;
        let existential = &statement.exist_fact_in_witness;
        if !existential.is_plain_exist()
            || existential.params_def_with_type().number_of_params() != 1
            || existential.facts().len() != 1
            || statement.equal_tos.len() != 1
        {
            return Ok(None);
        }
        let group = &existential.params_def_with_type().groups[0];
        if group.params.len() != 1 || !matches!(group.param_type, ParamType::Obj(_)) {
            return Ok(None);
        }
        if verification.proof_steps.len() != statement.proof.len()
            || verification.parameter_checks.len() != 1
            || verification.body_checks.len() != 1
            || verification.uniqueness_check.is_some()
        {
            return Err(
                "existential witness Result changed its parameter, proof-step, body, or uniqueness mapping"
                    .into(),
            );
        }

        let source_set = parameter_set(&group.param_type)?;
        let witness_object = &statement.equal_tos[0];
        let rendered_witness = render_obj(witness_object, &self.environment_stack)?;
        let proposition = render_existential_fact(existential, &self.environment_stack)?;

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            if self
                .environment_stack
                .symbol_names
                .insert(group.params[0].id(), rendered_witness.clone())
                .is_some()
            {
                return Err("existential witness reused a visible binder SymbolId".into());
            }
            self.environment_stack
                .existential_names
                .insert(group.params[0].name().to_string(), rendered_witness.clone());

            let mut proof_lines = Vec::with_capacity(verification.proof_steps.len() + 1);
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(factual) = proof_step.factual_success() else {
                    return Ok(None);
                };
                let Some(line) = self
                    .compile_fact_stmt_result_as_local_proof_step(factual, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                proof_lines.push(line);
            }

            let Some(parameter_check) = verification.parameter_checks[0].as_deref() else {
                return Err(
                    "existential membership witness has no parameter-check child Result".into(),
                );
            };
            let parameter_check = parameter_check.factual_success().ok_or_else(|| {
                "existential witness parameter check is not a successful fact Result".to_string()
            })?;
            let expected_parameter_fact: Fact = InFact::new(
                witness_object.clone(),
                source_set.clone(),
                statement.line_file.clone(),
            )
            .into();
            if parameter_check.fact().to_string() != expected_parameter_fact.to_string()
                || !parameter_check.store.infers.is_empty()
            {
                return Err(
                    "existential witness parameter check changed its instantiated requirement"
                        .into(),
                );
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(parameter_check)?
            else {
                return Ok(None);
            };

            let body_check = verification.body_checks[0]
                .factual_success()
                .ok_or_else(|| {
                    "existential witness body check is not a successful fact Result".to_string()
                })?;
            if !body_check.store.infers.is_empty() {
                return Ok(None);
            }
            let expected_body = render_fact(
                &existential.facts()[0].from_ref_to_cloned_fact(),
                &self.environment_stack,
            )?;
            let retained_body = render_fact(&body_check.fact(), &self.environment_stack)?;
            if retained_body != expected_body {
                return Err(format!(
                    "existential witness body check changed `{expected_body}` to `{retained_body}`"
                ));
            }
            let Some(body_proof) = self.construct_lean_proof_from_direct_fact_result(body_check)?
            else {
                return Ok(None);
            };

            let carrier_witness = if matches!(source_set, Obj::FnSet(_))
                || set_requires_heterogeneous_carrier(source_set)
            {
                format!("_, {rendered_witness}")
            } else {
                rendered_witness
            };
            proof_lines.push(format!(
                "exact ⟨{carrier_witness}, ({parameter_proof}), ({body_proof})⟩"
            ));
            Ok(Some(CompiledExistentialWitnessProofBody {
                proposition,
                proof_expression: format!("(by\n{})", indent_lines(&proof_lines.join("\n"), 2)),
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    /// `Combine`: resolve the exact existential source proof, introduce the
    /// selected object name, and publish each retained projection under the
    /// exact store FactId owned by this elimination Result.
    fn compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromExistFactResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if result.statement.fact.to_string() != verification.source_exist_fact.to_string() {
            return Err("existential elimination changed its source existential".into());
        }
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            None,
        )
    }

    /// `Combine`: the statement itself is the existential source. The adapter
    /// verifies that execution retained that exact binder and body before the
    /// shared elimination compiler consumes its recursively named children.
    fn compile_have_obj_by_exist_facts_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjByExistFactsStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let existential = &verification.source_exist_fact;
        if result.statement.param_def.to_string() != existential.params_def_with_type().to_string()
            || result
                .statement
                .facts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != existential
                    .facts()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("object-by-existential Result changed its binder or body facts".into());
        }
        let bindings = result.statement.param_def.collect_param_bindings();
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &bindings,
            &result.common,
            verification,
            None,
        )
    }

    /// `Combine`: the concrete predicate projection is retained as the source
    /// fact Result. The shared compiler obtains the witness only after that
    /// exact recursive `DefinitionProjection` proof has been constructed.
    fn compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromAtomicFactResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let source_result = verification
            .source_result
            .factual_success()
            .ok_or_else(|| {
                "predicate-backed existential elimination source is not factual".to_string()
            })?;
        let SuccessFactProofResult::BuiltinRule(source_builtin) = source_result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) = &source_builtin.evidence
        else {
            return Ok(false);
        };
        if evidence.fact.to_string() != result.statement.fact.to_string() {
            return Err("predicate-backed existential elimination changed its source fact".into());
        }
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            None,
        )
    }

    /// `Combine`: the nested theorem application constructs one local
    /// existential conclusion proof. This parent consumes that proof as its
    /// source and publishes only the selected witness projections.
    fn compile_obtain_obj_from_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromThmResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let source_result = verification
            .source_result
            .non_factual_success()
            .ok_or_else(|| {
                "theorem-backed existential elimination source is not a statement Result"
                    .to_string()
            })?;
        let SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(theorem_application)) =
            source_result
        else {
            return Err(
                "theorem-backed existential elimination retained another source statement".into(),
            );
        };
        if theorem_application.statement.name.to_string() != result.statement.thm_name.to_string()
            || theorem_application
                .statement
                .args
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != result
                    .statement
                    .args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err(
                "theorem-backed existential elimination changed its theorem application".into(),
            );
        }
        let Some(mut conclusions) = self
            .construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
                theorem_application,
            )?
        else {
            return Ok(false);
        };
        if conclusions.len() != 1 {
            return Err(
                "theorem-backed existential elimination requires one direct conclusion".into(),
            );
        }
        let source = conclusions
            .pop()
            .expect("one theorem conclusion was checked above");
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            Some(CompiledFactProofBody {
                fact: source.fact,
                proposition: source.proposition,
                proof_expression: source.proof_expression,
            }),
        )
    }

    /// Shared `Combine` for the currently reviewed existential-elimination
    /// shape. Statement-family adapters above own syntax-specific validation;
    /// this method owns the one source proof, witness binding, and two stored
    /// projection effects.
    fn compile_positive_single_witness_existential_elimination_result_to_lean_source(
        &mut self,
        introduced_bindings: &[SymbolBinding],
        common: &SuccessStmtCommonResult,
        verification: &SuccessVerifyExistentialEliminationResult,
        prepared_source_proof: Option<CompiledFactProofBody>,
    ) -> Result<bool, String> {
        let existential = &verification.source_exist_fact;
        if !existential.is_plain_exist()
            || existential.params_def_with_type().number_of_params() != 1
            || existential.facts().len() != 1
            || introduced_bindings.len() != 1
            || verification.witness_type_facts.len() != 1
            || verification.instantiated_body_facts.len() != 1
            || verification.includes_uniqueness
        {
            return Ok(false);
        }
        if !common.infers.rule_applications.is_empty()
            || common.infers.store_fact_outputs.iter().any(|output| {
                !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
            })
        {
            return Ok(false);
        }
        let expected_stored_facts = vec![
            verification.witness_type_facts[0].clone(),
            verification.instantiated_body_facts[0].clone(),
        ];
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &common.infers,
            &expected_stored_facts,
            "existential elimination projections",
        )?;

        let source_fact: Fact = existential.clone().into();
        let source_proof_body = if let Some(source_proof) = prepared_source_proof {
            source_proof
        } else {
            let source_result = verification
                .source_result
                .factual_success()
                .ok_or_else(|| {
                    "existential elimination source is not a successful fact Result".to_string()
                })?;
            if !source_result.store.infers.is_empty() {
                return Err("existential elimination source Result gained effects".into());
            }
            let Some(source_proof) =
                self.construct_lean_proof_from_direct_fact_result(source_result)?
            else {
                return Ok(false);
            };
            let fact = source_result.fact();
            CompiledFactProofBody {
                proposition: render_fact(&fact, &self.environment_stack)?,
                fact,
                proof_expression: source_proof,
            }
        };
        if !one_witness_existentials_are_alpha_equal(
            &source_proof_body.fact,
            &source_fact,
            &self.environment_stack,
        )? {
            return Err("existential elimination source Result changed its cited fact".into());
        }
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        if source_proof_body.proposition != source_proposition {
            return Err("existential elimination source proof changed its Lean proposition".into());
        }
        let typed_source_proof = format!(
            "(show {source_proposition} from {})",
            source_proof_body.proof_expression
        );

        let group = &existential.params_def_with_type().groups[0];
        if group.params.len() != 1 || !matches!(group.param_type, ParamType::Obj(_)) {
            return Ok(false);
        }
        let source_set = parameter_set(&group.param_type)?;
        let binding = &introduced_bindings[0];
        let witness_name = lean_identifier(binding.name());
        let mut result_environment_stack = self.environment_stack.clone();
        if result_environment_stack
            .symbol_names
            .insert(binding.id(), witness_name.clone())
            .is_some()
        {
            return Err(format!(
                "existential elimination reused SymbolId for `{}`",
                binding.name()
            ));
        }
        let mut source_template_environment_stack = result_environment_stack.clone();
        source_template_environment_stack
            .symbol_names
            .insert(group.params[0].id(), witness_name.clone());
        source_template_environment_stack
            .existential_names
            .insert(group.params[0].name().to_string(), witness_name.clone());

        let expected_requirement = format!(
            "Litex.In {witness_name} {}",
            render_obj(source_set, &result_environment_stack)?
        );
        let retained_requirement = render_fact(
            &verification.witness_type_facts[0],
            &result_environment_stack,
        )?;
        let expected_body = render_fact(
            &existential.facts()[0].from_ref_to_cloned_fact(),
            &source_template_environment_stack,
        )?;
        let retained_body = render_fact(
            &verification.instantiated_body_facts[0],
            &result_environment_stack,
        )?;
        if retained_requirement != expected_requirement || retained_body != expected_body {
            return Err("existential elimination changed a retained projection role".into());
        }

        // Only the selected object is visible after this Result. The source
        // existential binder above exists solely while validating the two
        // recursively retained projection children.
        self.environment_stack = result_environment_stack;

        let dynamic_carrier = set_requires_heterogeneous_carrier(source_set);
        let function_carrier = matches!(source_set, Obj::FnSet(_));
        let carrier_name = format!("__carrier_{witness_name}");
        let specification = if dynamic_carrier || function_carrier {
            self.declarations.push(format!(
                "noncomputable def {carrier_name} : {} := Classical.choose ({typed_source_proof})",
                if function_carrier { "Type 1" } else { "Type" }
            ));
            self.declarations.push(format!(
                "noncomputable def {witness_name} : {carrier_name} :=\n  Classical.choose (Classical.choose_spec ({typed_source_proof}))"
            ));
            format!("Classical.choose_spec (Classical.choose_spec ({typed_source_proof}))")
        } else {
            self.declarations.push(format!(
                "noncomputable def {witness_name} : ℂ := Classical.choose ({typed_source_proof})"
            ));
            format!("Classical.choose_spec ({typed_source_proof})")
        };

        let unfold = if dynamic_carrier || function_carrier {
            format!("{witness_name} {carrier_name}")
        } else {
            witness_name.clone()
        };
        for ((fact, fact_id), selector) in expected_stored_facts
            .iter()
            .zip(stored_fact_ids.iter())
            .zip([".1", ".2"])
        {
            let proposition = render_fact(fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  unfold {unfold}\n  exact ({specification}){selector}"
            ));
            self.environment_stack
                .fact_names
                .insert(*fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(*fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    fn compile_by_cases_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByCasesStmtResult,
    ) -> Result<bool, String> {
        let Some(proofs) = self.construct_lean_proofs_from_by_cases_stmt_result(result)? else {
            return Ok(false);
        };
        let fact_ids = validate_compiled_fact_proof_effects(
            &result.common.infers,
            &proofs,
            &self.environment_stack,
            "by-cases exported goals",
        )?;
        for (proof, fact_id) in proofs.into_iter().zip(fact_ids) {
            let Some(fact_id) = fact_id else {
                continue;
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := by\n  exact {}",
                proof.proposition, proof.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, proof.fact);
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: one coverage proof is replayed in every exported goal;
    /// every branch receives its own inherited compiler environment.
    fn construct_lean_proofs_from_by_cases_stmt_result(
        &mut self,
        result: &SuccessByCasesStmtResult,
    ) -> Result<Option<Vec<CompiledFactProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if result.statement.then_facts.len() != verification.then_facts.len()
            || result.statement.cases.len() != verification.branches.len()
            || result.statement.proofs.len() != verification.branches.len()
            || result.statement.impossible_facts.len() != verification.branches.len()
            || verification.goal_well_definedness.len() != verification.then_facts.len()
        {
            return Err("by-cases Result changed its goal or branch arity".into());
        }
        for (source, retained) in result
            .statement
            .then_facts
            .iter()
            .zip(verification.then_facts.iter())
        {
            if source.to_string() != retained.to_string() {
                return Err("by-cases verification changed an exported goal".into());
            }
            if !matches!(source, Fact::AtomicFact(_)) {
                return Ok(None);
            }
        }
        for (goal, well_definedness) in verification
            .then_facts
            .iter()
            .zip(verification.goal_well_definedness.iter())
        {
            validate_atomic_fact_well_definedness_result(well_definedness, goal)?;
        }

        let coverage = verification
            .coverage_check
            .factual_success()
            .ok_or_else(|| "by-cases coverage child is not factual".to_string())?;
        let expected_coverage: Fact = OrFact::new(
            verification
                .branches
                .iter()
                .map(|branch| branch.assumption.clone())
                .collect(),
            result.statement.line_file.clone(),
        )
        .into();
        if coverage.fact().to_string() != expected_coverage.to_string()
            || !coverage.store.infers.is_empty()
        {
            return Err("by-cases coverage child changed the ordered cases".into());
        }
        let Some(coverage_proof) = self.construct_lean_proof_from_direct_fact_result(coverage)?
        else {
            return Ok(None);
        };

        let case_names = (0..verification.branches.len())
            .map(|index| format!("__case{}", index + 1))
            .collect::<Vec<_>>();
        let mut compiled_goals = Vec::with_capacity(verification.then_facts.len());
        for (goal_index, goal) in verification.then_facts.iter().enumerate() {
            let mut proof_lines = vec!["by".to_string()];
            if verification.branches.len() == 1 {
                let case_type = render_fact(
                    &verification.branches[0].assumption.clone().into(),
                    &self.environment_stack,
                )?;
                proof_lines.push(format!(
                    "  have {} : {case_type} := {coverage_proof}",
                    case_names[0]
                ));
            } else {
                proof_lines.push(format!(
                    "  rcases ({coverage_proof}) with {}",
                    case_names.join(" | ")
                ));
            }

            for (branch_index, branch) in verification.branches.iter().enumerate() {
                if branch.assumption.to_string() != result.statement.cases[branch_index].to_string()
                    || branch.proof_steps.len() != result.statement.proofs[branch_index].len()
                {
                    return Err(format!(
                        "by-cases branch {branch_index} changed its assumption or proof-step order"
                    ));
                }
                self.environment_stack.push_inherited_environment();
                let branch_compilation = (|| {
                    let case_fact: Fact = branch.assumption.clone().into();
                    let stored_assumption_fact_id = validate_single_fact_store_output(
                        &branch.proof_scope.assumption_infers,
                        &case_fact,
                        "by-cases branch assumption",
                    )?;
                    if stored_assumption_fact_id != branch.assumption_fact_id {
                        return Err("by-cases branch assumption FactIds disagree".into());
                    }
                    self.environment_stack
                        .fact_names
                        .insert(branch.assumption_fact_id, case_names[branch_index].clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(branch.assumption_fact_id, case_fact.clone());

                    let expected_components = match &branch.assumption {
                        AndChainAtomicFact::AtomicFact(_) => Vec::new(),
                        AndChainAtomicFact::AndFact(and_fact) => and_fact
                            .facts
                            .iter()
                            .cloned()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact
                            .facts()
                            .map_err(|error| format!("invalid by-cases chain assumption: {error}"))?
                            .into_iter()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                    };
                    if expected_components.len() != branch.proof_scope.assumption_components.len() {
                        return Err("by-cases branch lost a structural assumption component".into());
                    }
                    let mut local_lines = Vec::new();
                    for (component_index, ((fact_id, retained), expected)) in branch
                        .proof_scope
                        .assumption_components
                        .iter()
                        .zip(expected_components.iter())
                        .enumerate()
                    {
                        if retained.to_string() != expected.to_string() {
                            return Err(
                                "by-cases branch changed a structural component position".into()
                            );
                        }
                        let component_name = format!(
                            "__case{}_component{}",
                            branch_index + 1,
                            component_index + 1
                        );
                        let component_type = render_fact(retained, &self.environment_stack)?;
                        let component_proof = conjunction_projection(
                            &format!("({})", case_names[branch_index]),
                            component_index,
                            expected_components.len(),
                        )?;
                        local_lines.push(format!(
                            "have {component_name} : {component_type} := by\n  exact {component_proof}"
                        ));
                        self.environment_stack
                            .fact_names
                            .insert(*fact_id, component_name);
                        self.environment_stack
                            .fact_propositions
                            .insert(*fact_id, retained.clone());
                    }
                    for (proof_step_index, proof_step) in branch.proof_steps.iter().enumerate() {
                        let Some(lines) = self.compile_stmt_result_as_local_proof_steps(
                            proof_step,
                            proof_step_index + 1,
                        )?
                        else {
                            return Ok(None);
                        };
                        local_lines.extend(lines);
                    }

                    let exit_proof = match &branch.exit {
                        SuccessVerifyByCaseBranchExitResult::Conclusions(exit) => {
                            if result.statement.impossible_facts[branch_index].is_some()
                                || exit.checks.len() != verification.then_facts.len()
                            {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its conclusion exit"
                                ));
                            }
                            let conclusion =
                                exit.checks[goal_index].factual_success().ok_or_else(|| {
                                    format!(
                                        "by-cases branch {branch_index} conclusion is not factual"
                                    )
                                })?;
                            if conclusion.fact().to_string() != goal.to_string() {
                                return Err(format!(
                                    "by-cases branch {branch_index} conclusion changed goal `{goal}` to `{}`",
                                    conclusion.fact()
                                ));
                            }
                            validate_scoped_fact_check_result(
                                conclusion,
                                goal,
                                &format!("by-cases branch {branch_index} conclusion"),
                            )?;
                            let Some(proof) =
                                self.construct_lean_proof_from_direct_fact_result(conclusion)?
                            else {
                                return Ok(None);
                            };
                            proof
                        }
                        SuccessVerifyByCaseBranchExitResult::Contradiction(exit) => {
                            let Some(expected_impossible) =
                                &result.statement.impossible_facts[branch_index]
                            else {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its contradiction exit"
                                ));
                            };
                            if exit.impossible_fact.to_string() != expected_impossible.to_string() {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its impossible fact"
                                ));
                            }
                            let Some(contradiction) = self
                                .construct_lean_contradiction_from_result(
                                    &exit.impossible_fact,
                                    &exit.contradiction,
                                )?
                            else {
                                return Ok(None);
                            };
                            format!("False.elim ({contradiction})")
                        }
                    };
                    Ok(Some((local_lines, exit_proof)))
                })();
                self.environment_stack.pop_local_environment();
                let Some((local_lines, exit_proof)) = branch_compilation? else {
                    return Ok(None);
                };
                if verification.branches.len() == 1 {
                    for line in local_lines {
                        proof_lines.push(indent_lines(&line, 2));
                    }
                    proof_lines.push(format!("  exact {exit_proof}"));
                } else {
                    proof_lines.push("  ·".into());
                    for line in local_lines {
                        proof_lines.push(indent_lines(&line, 4));
                    }
                    proof_lines.push(format!("    exact {exit_proof}"));
                }
            }
            let proposition = self.render_fact_using_well_definedness_result(
                &verification.goal_well_definedness[goal_index],
                goal,
            )?;
            compiled_goals.push(CompiledFactProofBody {
                fact: goal.clone(),
                proposition,
                proof_expression: format!("({})", proof_lines.join("\n")),
            });
        }
        Ok(Some(compiled_goals))
    }

    fn compile_by_contra_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByContraStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_contra_stmt_result(result)? else {
            return Ok(false);
        };
        let [fact_id] = validate_compiled_fact_proof_effects(
            &result.common.infers,
            std::slice::from_ref(&proof),
            &self.environment_stack,
            "by-contra exported goal",
        )?
        .try_into()
        .map_err(|_| "by-contra effect validation changed its output arity".to_string())?;
        let Some(fact_id) = fact_id else {
            return Ok(true);
        };
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: install the exact reverse-assumption FactId in one inherited
    /// environment, compile the ordered proof-step Results, then combine the
    /// two retained contradiction checks.
    fn construct_lean_proof_from_by_contra_stmt_result(
        &mut self,
        result: &SuccessByContraStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.to_prove.to_string() != result.statement.to_prove.to_string()
            || verification.proof_steps.len() != result.statement.proof.len()
            || verification.impossible_fact.to_string()
                != result.statement.impossible_fact.to_string()
            || !verification.proof_scope.assumption_components.is_empty()
        {
            return Err("by-contra Result changed its target or proof structure".into());
        }
        let Fact::AtomicFact(target_atomic) = &verification.to_prove else {
            return Ok(None);
        };
        let expected_reverse: Fact = target_atomic
            .logical_negation()
            .map_err(|_| "by-contra target has no atomic negation".to_string())?
            .into();
        if verification.reverse_assumption.to_string() != expected_reverse.to_string() {
            return Err("by-contra Result changed its reverse assumption".into());
        }
        let stored_reverse_fact_id = validate_single_fact_store_output(
            &verification.proof_scope.assumption_infers,
            &verification.reverse_assumption,
            "by-contra reverse assumption",
        )?;
        if stored_reverse_fact_id != verification.reverse_assumption_fact_id {
            return Err("by-contra reverse-assumption FactIds disagree".into());
        }
        self.environment_stack.push_inherited_environment();
        let compilation: Result<Option<String>, String> = (|| {
            self.environment_stack
                .fact_names
                .insert(verification.reverse_assumption_fact_id, "__reverse".into());
            self.environment_stack.fact_propositions.insert(
                verification.reverse_assumption_fact_id,
                verification.reverse_assumption.clone(),
            );
            let mut local_lines = Vec::new();
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                local_lines.extend(lines);
            }
            let Some(contradiction) = self.construct_lean_contradiction_from_result(
                &verification.impossible_fact,
                &verification.contradiction,
            )?
            else {
                return Ok(None);
            };
            let mut proof_lines = vec!["by".to_string(), "  classical".to_string()];
            if atomic_fact_is_logically_negated(target_atomic) {
                let reverse_type =
                    render_fact(&verification.reverse_assumption, &self.environment_stack)?;
                proof_lines
                    .push("  exact Classical.byContradiction (fun __negated_goal => by".into());
                proof_lines.push(format!(
                    "    have __reverse : {reverse_type} := Classical.byContradiction (fun __not_reverse => __negated_goal __not_reverse)"
                ));
                for line in local_lines {
                    proof_lines.push(indent_lines(&line, 4));
                }
                proof_lines.push(format!("    exact {contradiction})"));
            } else {
                proof_lines.push("  by_contra __reverse".into());
                for line in local_lines {
                    proof_lines.push(indent_lines(&line, 2));
                }
                proof_lines.push(format!("  exact {contradiction}"));
            }
            Ok(Some(format!("({})", proof_lines.join("\n"))))
        })();
        self.environment_stack.pop_local_environment();
        let Some(proof_expression) = compilation? else {
            return Ok(None);
        };
        Ok(Some(CompiledFactProofBody {
            fact: verification.to_prove.clone(),
            proposition: render_fact(&verification.to_prove, &self.environment_stack)?,
            proof_expression,
        }))
    }

    fn construct_lean_contradiction_from_result(
        &mut self,
        impossible_fact: &AtomicFact,
        contradiction: &SuccessVerifyContradictionResult,
    ) -> Result<Option<String>, String> {
        let impossible = contradiction
            .impossible_check
            .factual_success()
            .ok_or_else(|| "contradiction positive child is not factual".to_string())?;
        let negated = contradiction
            .negated_impossible_check
            .factual_success()
            .ok_or_else(|| "contradiction negated child is not factual".to_string())?;
        let impossible_target: Fact = impossible_fact.clone().into();
        let expected_negated: Fact = impossible_fact
            .logical_negation()
            .map_err(|_| "contradiction fact has no atomic negation".to_string())?
            .into();
        if impossible.fact().to_string() != impossible_target.to_string()
            || negated.fact().to_string() != expected_negated.to_string()
            || !impossible.store.infers.is_empty()
            || !negated.store.infers.is_empty()
        {
            return Err("contradiction Result changed one of its complementary facts".into());
        }
        let Some(impossible_proof) =
            self.construct_lean_proof_from_direct_fact_result(impossible)?
        else {
            return Ok(None);
        };
        let Some(negated_proof) = self.construct_lean_proof_from_direct_fact_result(negated)?
        else {
            return Ok(None);
        };
        if atomic_fact_is_logically_negated(impossible_fact) {
            let impossible_type = render_fact(&impossible_target, &self.environment_stack)?;
            Ok(Some(format!(
                "(({impossible_proof} : {impossible_type}) ({negated_proof}))"
            )))
        } else {
            let negated_type = render_fact(&expected_negated, &self.environment_stack)?;
            Ok(Some(format!(
                "(({negated_proof} : {negated_type}) ({impossible_proof}))"
            )))
        }
    }

    fn compile_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        self.install_atomic_fact_well_definedness_store_results(result)?;
        if self.compile_object_reflexivity_fact_result(result)? {
            return Ok(());
        }
        if self.compile_rational_normalization_fact_result(result)? {
            return Ok(());
        }
        if self.compile_exact_fact_citation_result(result)? {
            return Ok(());
        }
        if self.compile_closed_natural_membership_fact_result(result)? {
            return Ok(());
        }
        let fact = LitexToLeanIrBuilder::new()
            .compile_fact_stmt_result(result)
            .map_err(|error| format!("StmtResult-to-Lean fact compilation failed: {error:?}"))?;
        construct_lean_declarations_for_compatibility_fact_result(
            &fact,
            &mut self.declarations,
            &mut self.next_fact_name_index,
            &mut self.environment_stack,
        )
    }

    /// Some object-WD constructors intentionally store a fact for later
    /// statements. Function application is the important example: checking
    /// `f(x)` stores `f(x) $in ReturnSet` under a real FactId. These are not
    /// display-only WD details, so the compiler installs their proof bindings
    /// before compiling the enclosing fact proof.
    fn install_atomic_fact_well_definedness_store_results(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        let Some(recursive) = result.well_definedness.recursive.as_deref() else {
            return Ok(());
        };
        let SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) = recursive else {
            return Ok(());
        };
        let certificate = LitexToLeanIrBuilder::new()
            .compile_fact_well_definedness_result_for_lean_rendering(
                &result.well_definedness,
                &result.fact(),
            )
            .map_err(|error| error.to_string())?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let installation = (|| {
            let mut visited = HashSet::new();
            for argument in &atomic.arguments {
                install_object_well_definedness_store_results(
                    argument.result.as_ref(),
                    &mut self.environment_stack,
                    &mut visited,
                )?;
            }
            Ok(())
        })();
        self.environment_stack.well_definedness = previous_well_definedness;
        installation
    }

    fn compile_object_reflexivity_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) = &builtin.evidence else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        if !builtin.subgoals.is_empty() {
            return Err("object reflexivity gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("object-reflexivity evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("object-reflexivity evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
            return Err("object-reflexivity evidence changed its equality endpoints".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        let proof = format!(
            "Litex.Same.refl {}",
            self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?
        );
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    fn compile_rational_normalization_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::RationalNormalization(evidence)) = &builtin.evidence else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        if !builtin.subgoals.is_empty() {
            return Err("rational normalization gained unexpected proof children".into());
        }
        let source_fact = result.fact();
        if evidence.expected_target.to_string() != source_fact.to_string() {
            return Err("rational-normalization evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
            return Err("rational-normalization evidence targets a non-equality fact".into());
        };
        if obj_equality_key(&equality.left)
            != obj_equality_key(&evidence.left_evaluation.expression)
            || obj_equality_key(&equality.right)
                != obj_equality_key(&evidence.right_evaluation.expression)
        {
            return Err("rational-normalization evidence changed an equality endpoint".into());
        }
        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
        if evidence.left_evaluation.value.normalized_value
            != evidence.right_evaluation.value.normalized_value
        {
            return Err("rational-normalization evidence retained unequal normal forms".into());
        }
        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.left)?;
        self.render_object_using_well_definedness_from_fact_result(result, &equality.right)?;
        self.compile_stored_fact_without_inference(
            result,
            "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                .to_string(),
        )?;
        Ok(true)
    }

    fn render_object_using_well_definedness_from_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
        object: &Obj,
    ) -> Result<String, String> {
        let certificate = LitexToLeanIrBuilder::new()
            .compile_fact_well_definedness_result_for_lean_rendering(
                &result.well_definedness,
                &result.fact(),
            )
            .map_err(|error| error.to_string())?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_obj(object, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    fn render_fact_using_well_definedness_result(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
        fact: &Fact,
    ) -> Result<String, String> {
        let certificate = LitexToLeanIrBuilder::new()
            .compile_fact_well_definedness_result_for_lean_rendering(result, fact)
            .map_err(|error| error.to_string())?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_fact(fact, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    fn compile_stored_fact_without_inference(
        &mut self,
        result: &SuccessFactStmtResult,
        proof: String,
    ) -> Result<(), String> {
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("fact changed between verification and store".into());
        }
        let fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored fact has no FactId".to_string())?;
        if !result.store.infers.rule_applications.is_empty() {
            return Err("zero-inference fact retained unexpected typed infer rules".into());
        }
        match result.store.infers.store_fact_outputs.as_slice() {
            [store]
                if store.fact_id == Some(fact_id)
                    && store.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
                    && store.inferred_facts.is_empty()
                    && store.inferred_fact_ids.is_empty() => {}
            [] if self
                .environment_stack
                .fact_propositions
                .get(&fact_id)
                .is_some_and(|stored| stored.to_string() == source_fact.to_string()) => {}
            _ => {
                return Err(
                    "zero-inference fact store output disagrees with the statement store".into(),
                );
            }
        }
        // The object renderer has not yet been migrated off its legacy WD
        // certificate shape. Derive that temporary view from this exact
        // Result, use it only while rendering this proposition, then restore
        // the surrounding compiler environment even when rendering fails.
        let previous_well_definedness = if matches!(source_fact, Fact::AtomicFact(_)) {
            let certificate = LitexToLeanIrBuilder::new()
                .compile_fact_stmt_result(result)
                .map_err(|error| error.to_string())?
                .well_definedness;
            self.environment_stack.well_definedness.replace(certificate)
        } else {
            None
        };
        let rendered_proposition = render_fact(&source_fact, &self.environment_stack);
        if matches!(source_fact, Fact::AtomicFact(_)) {
            self.environment_stack.well_definedness = previous_well_definedness;
        }
        let proposition = rendered_proposition?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        let declaration = if matches!(source_fact, Fact::ForallFact(_)) {
            format!("theorem {theorem_name} :\n    {proposition} := {proof}")
        } else {
            format!("theorem {theorem_name} : {proposition} := by\n  exact {proof}")
        };
        self.declarations.push(declaration);
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact);
        self.next_fact_name_index += 1;
        Ok(())
    }

    fn compile_exact_fact_citation_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::Fact(citation) = result.proof() else {
            return Ok(false);
        };
        if citation.equality_transport.is_some()
            || citation.fact_transformation.is_some()
            || citation.checked_function_definition_reduction.is_some()
            || citation.definition_reduction.is_some()
        {
            return Ok(false);
        }
        let Some(source_fact_id) = citation.source_fact_id else {
            return Ok(false);
        };
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        // FactId is the citation identity. `resolve_fact_citation` additionally
        // checks that the retained proposition is unchanged, including
        // alpha-equivalent forall binders, before exposing its Lean name.
        let proof = resolve_fact_citation(&source_fact_id, &source_fact, &self.environment_stack)?;
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        }
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }

    /// Direct `Leaf + Combine` compilation for a closed expression proved to
    /// belong to `N`. This is the persistent `2 + 3 $in N` tracer path: its WD
    /// tree, recursive evaluation, store identity, and infer edge are read
    /// from `SuccessFactStmtResult` without constructing backend statement or
    /// fact IR nodes.
    fn compile_closed_natural_membership_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = &builtin.evidence else {
            return Ok(false);
        };
        if evidence.target_set != StandardSet::N {
            return Ok(false);
        }
        if !builtin.subgoals.is_empty() {
            return Err("closed natural membership gained unexpected proof subgoals".into());
        }

        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string()
            || evidence.expected_target.to_string() != source_fact.to_string()
        {
            return Err(
                "closed natural membership changed between verification, proof, and store".into(),
            );
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &source_fact else {
            return Err("closed natural membership proof retained a non-membership target".into());
        };
        if !matches!(&membership.set, Obj::StandardSet(StandardSet::N))
            || obj_equality_key(&membership.element)
                != obj_equality_key(&evidence.evaluation.expression)
        {
            return Err(
                "closed natural membership changed its expression or target carrier".into(),
            );
        }

        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        validate_success_evaluate_obj_result(&evidence.evaluation)?;

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored closed natural membership has no FactId".to_string())?;
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let proof = render_closed_numeric_membership_from_result(
            &source_fact,
            evidence.target_set,
            &evidence.evaluation,
            &self.environment_stack,
        )?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_natural_membership_infer_result(
            &source_fact,
            source_fact_id,
            &result.store.infers,
        )?;
        Ok(true)
    }

    fn compile_natural_membership_infer_result(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let applications = infers
            .rule_applications
            .iter()
            .filter(|application| {
                application.rule == InferRule::NaturalMembershipImpliesNonnegative
            })
            .collect::<Vec<_>>();
        if applications.len() != 1 {
            return Err(format!(
                "closed natural membership expected one typed nonnegative inference, retained {}",
                applications.len()
            ));
        }
        let application = applications[0];
        if application.premises.len() != 1
            || application.premises[0].fact_id != Some(source_fact_id)
            || application.premises[0].fact.to_string() != source_fact.to_string()
        {
            return Err(
                "natural-membership inference no longer cites the exact stored source FactId"
                    .into(),
            );
        }
        if application.conclusions.len() != 1 {
            return Err("natural-membership inference must retain one conclusion".into());
        }
        let conclusion = &application.conclusions[0];
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "natural-membership inference conclusion has no FactId".to_string())?;
        let conclusion_retains_its_store =
            conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id == Some(conclusion_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == conclusion.fact.to_string()
            });
        if !conclusion_retains_its_store {
            return Err("natural-membership inference conclusion lost its store layer".into());
        }
        let output_retains_conclusion = infers.store_fact_outputs.iter().any(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    fact.to_string() == conclusion.fact.to_string()
                        && *fact_id == Some(conclusion_fact_id)
                })
                || (output.itself_and_why_itself_is_stored.0.to_string()
                    == conclusion.fact.to_string()
                    && output.fact_id == Some(conclusion_fact_id))
        });
        if !output_retains_conclusion {
            return Err(
                "typed natural-membership inference and ordered store effects disagree".into(),
            );
        }

        let source_theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .ok_or_else(|| "stored source FactId is unavailable to its inference".to_string())?
            .clone();
        let conclusion_proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
        let conclusion_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {conclusion_theorem_name} : {conclusion_proposition} := by\n  exact Litex.Rules.nonnegativeOfInN ({source_theorem_name})"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, conclusion_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.next_fact_name_index += 1;
        Ok(())
    }

    fn unsupported_success_stmt_result(&self, result: &SuccessStmtResult) -> Result<(), String> {
        let statement = result.statement();
        Err(format!(
            "StmtResult-to-Lean compiler does not support statement kind `{}` at {:?}",
            statement.stmt_type_name(),
            statement.line_file()
        ))
    }

    fn compile_sketch_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessSketchStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("a `sketch` unexpectedly exported facts to its parent environment".into());
        }
        let proof = result.proof.as_ref().ok_or_else(|| {
            "a successful `sketch` retained no recursive proof result".to_string()
        })?;
        if !proof.proof_scope.assumption_infers.is_empty()
            || !proof.proof_scope.assumption_components.is_empty()
        {
            return Err("a `sketch` retained unexpected local assumptions".into());
        }
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("a `sketch` result changed its source proof-step order".into());
        }

        let nested_declarations =
            self.compile_stmt_results_in_new_local_environment(&proof.proof_steps)?;
        self.next_sketch_namespace_index += 1;
        let namespace = format!("__Sketch{:02}", self.next_sketch_namespace_index);
        self.declarations.push(format!(
            "namespace {namespace}\n\n{}\n\nend {namespace}",
            nested_declarations.join("\n\n")
        ));
        Ok(())
    }

    /// `Combine`: compile each retained proof-step Result inside one inherited
    /// compiler environment, then wrap the retained conclusion proof in the
    /// persistent theorem introduced by `claim`.
    fn compile_claim_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessClaimStmtResult,
    ) -> Result<bool, String> {
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &result.verification else {
            return Ok(false);
        };
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            verification,
        )?
        else {
            return Ok(false);
        };

        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.len() != 1
        {
            return Err("ordinary `claim` must retain exactly one outer store effect".into());
        }
        let stored = &result.common.infers.store_fact_outputs[0];
        if stored.itself_and_why_itself_is_stored.0.to_string() != verification.fact.to_string()
            || !stored.inferred_facts.is_empty()
            || !stored.inferred_fact_ids.is_empty()
        {
            return Err("ordinary `claim` outer store changed its target or inferred facts".into());
        }
        let fact_id = stored
            .fact_id
            .ok_or_else(|| "ordinary `claim` outer store has no FactId".to_string())?;

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, verification.fact.clone());
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: an `example` owns the same recursive proof body as a claim,
    /// but intentionally publishes neither a FactId nor an outer environment
    /// effect.
    fn compile_example_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessExampleStmtResult,
    ) -> Result<bool, String> {
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &result.verification else {
            return Ok(false);
        };
        if !result.common.infers.is_empty() {
            return Err("an ordinary `example` unexpectedly exported environment effects".into());
        }
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            verification,
        )?
        else {
            return Ok(false);
        };

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        self.declarations.push(format!(
            "example : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: read the theorem's binder WD, proof-scope assumptions,
    /// ordered proof steps, conclusion checks, and outer store directly. This
    /// first binder-bearing tranche accepts ordinary object parameters with
    /// reviewed standard-set carriers. Other binder representations remain on
    /// the explicit compatibility path.
    fn compile_named_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let parameters = verification
            .forall_fact
            .params_def_with_type
            .collect_param_bindings_with_types();
        if !verification.forall_fact.dom_facts.is_empty()
            || parameters.iter().any(|(_, parameter_type)| {
                !matches!(parameter_type, ParamType::Set(_) | ParamType::Obj(_))
            })
            || verification
                .forall_fact
                .then_facts
                .iter()
                .any(|conclusion| {
                    !fact_is_supported_by_direct_named_theorem(&conclusion.clone().to_fact())
                })
        {
            return Ok(false);
        }
        if verification.name != result.statement.name
            || verification.forall_fact.to_string() != result.statement.forall_fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
            || verification.conclusion_checks.len() != verification.forall_fact.then_facts.len()
        {
            return Err("named theorem Result changed its declaration or child order".into());
        }
        if verification.forall_fact.then_facts.is_empty() {
            return Err("named theorem retained no conclusions".into());
        }
        if !verification.proof_scope.assumption_components.is_empty() {
            return Ok(false);
        }
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(well_definedness)) =
            verification.well_definedness.recursive.as_deref()
        else {
            return Err("named theorem has no recursive forall well-definedness".into());
        };
        let well_defined_parameters = well_definedness
            .binder
            .parameter_groups
            .iter()
            .flat_map(|group| {
                group
                    .parameters
                    .iter()
                    .map(move |parameter| (group, parameter))
            })
            .collect::<Vec<_>>();
        if well_definedness.statement.to_string() != verification.forall_fact.to_string()
            || !well_definedness.premises.is_empty()
            || well_defined_parameters.len() != parameters.len()
            || well_definedness.conclusions.len() != verification.forall_fact.then_facts.len()
        {
            return Err("named theorem well-definedness changed its forall structure".into());
        }
        for (parameter_index, ((binding, parameter_type), (group, parameter))) in parameters
            .iter()
            .zip(well_defined_parameters.iter())
            .enumerate()
        {
            if group.group_index >= well_definedness.binder.parameter_groups.len()
                || group.parameter_type.to_string() != parameter_type.to_string()
                || parameter.symbol_id != Some(binding.id())
            {
                return Err(format!(
                    "named theorem binder parameter {parameter_index} changed its type or SymbolId"
                ));
            }
            match parameter_type {
                ParamType::Set(_) => {
                    validate_set_parameter_premise(binding.id(), &parameter.proposition)?;
                }
                ParamType::Obj(expected_set) => {
                    validate_object_parameter_premise(
                        binding.id(),
                        expected_set,
                        &parameter.proposition,
                    )?;
                }
                ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    unreachable!("refined set parameters were excluded above")
                }
            }
            validate_atomic_fact_well_definedness_result(
                parameter.well_definedness.as_ref(),
                &parameter.proposition,
            )?;
            validate_single_fact_store_output(
                &parameter.infers,
                &parameter.proposition,
                "named theorem binder WD",
            )?;
        }
        for (conclusion_index, (conclusion, expected)) in well_definedness
            .conclusions
            .iter()
            .zip(verification.forall_fact.then_facts.iter())
            .enumerate()
        {
            let expected = expected.clone().to_fact();
            if conclusion.proposition.to_string() != expected.to_string() {
                return Err(format!(
                    "named theorem WD conclusion {conclusion_index} changed its proposition"
                ));
            }
            validate_direct_named_theorem_conclusion_well_definedness(
                conclusion.well_definedness.as_ref(),
                &conclusion.proposition,
            )?;
            validate_success_store_fact_result(
                &conclusion.store,
                &conclusion.proposition,
                "named theorem conclusion WD",
            )?;
        }

        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.len() > 1
        {
            return Ok(false);
        }
        if result.common.infers.store_fact_outputs.is_empty() {
            return Err("named theorem has no outer store effect".into());
        }
        let stored = &result.common.infers.store_fact_outputs[0];
        let theorem_fact: Fact = verification.forall_fact.clone().into();
        if stored.itself_and_why_itself_is_stored.0.to_string() != theorem_fact.to_string()
            || !stored.inferred_facts.is_empty()
            || !stored.inferred_fact_ids.is_empty()
        {
            return Ok(false);
        }
        let theorem_fact_id = stored
            .fact_id
            .ok_or_else(|| "named theorem outer store has no FactId".to_string())?;

        if !verification
            .proof_scope
            .assumption_infers
            .rule_applications
            .is_empty()
            || verification
                .proof_scope
                .assumption_infers
                .store_fact_outputs
                .iter()
                .any(|output| {
                    !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
                })
        {
            return Ok(false);
        }
        let parameter_facts = well_defined_parameters
            .iter()
            .map(|(_, parameter)| parameter.proposition.clone())
            .collect::<Vec<_>>();
        let parameter_fact_ids = exact_ordered_fact_ids_from_store_results(
            &verification.proof_scope.assumption_infers,
            &parameter_facts,
            "named theorem proof-scope parameters",
        )?;

        self.environment_stack.push_inherited_environment();
        let compilation: Result<Option<CompiledNamedTheoremProofBody>, String> = (|| {
            let mut binder_declarations = Vec::new();
            let mut binder_intro_names = Vec::new();
            for (parameter_index, (((binding, parameter_type), parameter), fact_id)) in parameters
                .iter()
                .zip(parameter_facts.iter())
                .zip(parameter_fact_ids.iter())
                .enumerate()
            {
                let parameter_name = lean_identifier(binding.name());
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), parameter_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "named theorem binder reused SymbolId `{:?}`",
                        binding.id()
                    ));
                }
                if matches!(parameter_type, ParamType::Set(_)) {
                    validate_set_parameter_premise(binding.id(), parameter)?;
                    binder_declarations.push(format!("({parameter_name} : Litex.Set)"));
                    binder_intro_names.push(parameter_name);
                    continue;
                }

                let parameter_set = parameter_set(parameter_type)?;
                let rendered_parameter_set = render_obj(parameter_set, &self.environment_stack)?;
                let carrier_name = format!(
                    "__carrier{}_{}",
                    self.next_fact_name_index,
                    parameter_index + 1
                );
                match parameter_set {
                    Obj::FnSet(_) => {
                        binder_declarations.push(format!("{{{carrier_name} : Type 1}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                    set if set_requires_heterogeneous_carrier(set) => {
                        binder_declarations.push(format!("{{{carrier_name} : Type}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                    _ => binder_declarations.push(format!("({parameter_name} : ℂ)")),
                }
                binder_intro_names.push(parameter_name.clone());
                let rendered_parameter_fact = render_fact(parameter, &self.environment_stack)?;
                let expected_parameter_fact =
                    format!("Litex.In {parameter_name} {rendered_parameter_set}");
                if rendered_parameter_fact != expected_parameter_fact {
                    return Err(format!(
                        "named theorem parameter evidence mismatch: expected `{expected_parameter_fact}`, found `{rendered_parameter_fact}`"
                    ));
                }
                let hypothesis_name =
                    format!("__h{}_{}", self.next_fact_name_index, parameter_index + 1);
                binder_declarations
                    .push(format!("({hypothesis_name} : {rendered_parameter_fact})"));
                binder_intro_names.push(hypothesis_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, hypothesis_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, parameter.clone());
                install_parameter_fact_aliases(
                    binding.id(),
                    parameter,
                    &hypothesis_name,
                    parameter_set,
                    &mut self.environment_stack,
                )?;
            }

            let mut proof_lines = Vec::with_capacity(
                verification.proof_steps.len() + verification.conclusion_checks.len() + 1,
            );
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                proof_lines.extend(lines);
            }

            let mut conclusion_names = Vec::new();
            let mut conclusion_types = Vec::new();
            for (conclusion_index, (conclusion, expected_conclusion)) in verification
                .conclusion_checks
                .iter()
                .zip(verification.forall_fact.then_facts.iter())
                .enumerate()
            {
                let conclusion = conclusion
                    .factual_success()
                    .ok_or_else(|| "named theorem conclusion is not factual".to_string())?;
                let expected_conclusion = expected_conclusion.clone().to_fact();
                if conclusion.fact().to_string() != expected_conclusion.to_string()
                    || !conclusion.store.infers.is_empty()
                {
                    return Err(
                        "named theorem conclusion changed its target or gained effects".into(),
                    );
                }
                let Some(conclusion_proof) =
                    self.construct_lean_proof_from_direct_fact_result(conclusion)?
                else {
                    return Ok(None);
                };
                let proposition = render_fact(&expected_conclusion, &self.environment_stack)?;
                let conclusion_name =
                    format!("__c{}_{}", self.next_fact_name_index, conclusion_index);
                proof_lines.push(format!(
                    "have {conclusion_name} : {proposition} := {conclusion_proof}"
                ));
                conclusion_names.push(conclusion_name);
                conclusion_types.push(proposition);
            }
            if conclusion_names.len() == 1 {
                proof_lines.push(format!("exact {}", conclusion_names[0]));
            } else {
                proof_lines.push(format!("exact ⟨{}⟩", conclusion_names.join(", ")));
            }
            Ok(Some(CompiledNamedTheoremProofBody {
                binder_declarations,
                binder_intro_names,
                proof_lines,
                conclusion_type: conjunction(&conclusion_types),
            }))
        })();
        self.environment_stack.pop_local_environment();
        let Some(body) = compilation? else {
            return Ok(false);
        };

        let theorem_name = lean_identifier(&verification.name);
        let theorem_type = if body.binder_declarations.is_empty() {
            body.conclusion_type
        } else {
            format!(
                "∀ {},\n      {}",
                body.binder_declarations.join(" "),
                body.conclusion_type
            )
        };
        let intro = if body.binder_intro_names.is_empty() {
            String::new()
        } else {
            format!("intro {}\n", body.binder_intro_names.join(" "))
        };
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {theorem_type} := by\n{}",
            indent_lines(&format!("{intro}{}", body.proof_lines.join("\n")), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(theorem_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(theorem_fact_id, theorem_fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: instantiate one previously compiled Litex theorem by its
    /// exact source FactId, combine the ordered argument-membership proofs,
    /// and publish each direct conclusion under the exact store FactId
    /// retained by this statement Result.
    fn compile_litex_theorem_instantiation_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<bool, String> {
        let Some(conclusions) =
            self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
        else {
            return Ok(false);
        };
        for conclusion in conclusions {
            let fact_id = conclusion.retained_fact_id.ok_or_else(|| {
                format!(
                    "top-level by-thm conclusion `{}` has no retained FactId",
                    conclusion.fact
                )
            })?;
            let conclusion_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {conclusion_name} : {} := by\n  exact {}",
                conclusion.proposition, conclusion.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, conclusion_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, conclusion.fact);
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: construct the exact ordered theorem conclusions without
    /// publishing them into the caller's compiler environment. The enclosing
    /// statement decides whether those Result-owned FactIds become visible or
    /// remain local to another proof layer.
    fn construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<Option<Vec<CompiledLitexTheoremInstantiationConclusionProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.theorem_source != "litex"
            || verification.mode != "release_all"
            || result.statement.selected_facts.is_some()
            || verification.selected_fact.is_some()
            || !verification.temporary_then_facts.is_empty()
            || !verification.requirement_roles.is_empty()
            || !verification.requirement_checks.is_empty()
            || !verification.domain_facts.is_empty()
            || !verification.domain_checks.is_empty()
        {
            return Ok(None);
        }
        if verification.theorem != result.statement.name.to_string()
            || verification.arguments
                != result
                    .statement
                    .args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("by-thm Result changed its theorem name or argument order".into());
        }
        let source_fact_id = verification
            .source_fact_id
            .ok_or_else(|| "by-thm Result has no source theorem FactId".to_string())?;
        let source_fact = self
            .environment_stack
            .fact_propositions
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| format!("by-thm cited unavailable source FactId `{source_fact_id}`"))?;
        let Fact::ForallFact(source_forall) = &source_fact else {
            return Err("by-thm source FactId does not identify a forall fact".into());
        };
        let source_parameters = source_forall
            .params_def_with_type
            .collect_param_bindings_with_types();
        if !source_forall.dom_facts.is_empty()
            || source_parameters.iter().any(|(_, parameter_type)| {
                !matches!(parameter_type, ParamType::Obj(Obj::StandardSet(_)))
            })
        {
            return Ok(None);
        }
        if source_parameters.len() != result.statement.args.len()
            || source_forall.then_facts.len() != verification.direct_conclusions.len()
            || verification.direct_conclusions.is_empty()
        {
            return Err("by-thm Result changed its source theorem arity".into());
        }
        let Some(argument_verification) = &verification.argument_verification else {
            return Err("by-thm Result has no argument verification children".into());
        };
        if !argument_verification.infers.is_empty()
            || argument_verification.checks.len() != source_parameters.len()
        {
            return Ok(None);
        }

        let direct_conclusion_strings = verification
            .direct_conclusions
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        if verification.stored_then_facts != direct_conclusion_strings
            || verification.parent_stored_facts != direct_conclusion_strings
        {
            return Err("by-thm Result changed its direct conclusion order".into());
        }
        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
            || !result.common.infers.rule_applications.is_empty()
        {
            return Ok(None);
        }
        if result.common.infers.store_fact_outputs.len() != verification.direct_conclusions.len() {
            return Err("by-thm Result changed its direct conclusion store count".into());
        }
        let conclusion_fact_ids = result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .zip(verification.direct_conclusions.iter())
            .map(|(stored, expected)| {
                if stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                    return Err(
                        "by-thm Result changed a direct conclusion store proposition".into(),
                    );
                }
                Ok(stored.fact_id)
            })
            .collect::<Result<Vec<_>, String>>()?;

        let theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| format!("by-thm source FactId `{source_fact_id}` has no Lean name"))?;
        let mut application_parts = vec![theorem_name];
        for (parameter_index, (((_, parameter_type), argument), check)) in source_parameters
            .iter()
            .zip(result.statement.args.iter())
            .zip(argument_verification.checks.iter())
            .enumerate()
        {
            let parameter_set = parameter_set(parameter_type)?;
            let rendered_argument = render_obj(argument, &self.environment_stack)?;
            let expected_parameter_fact = format!(
                "Litex.In {rendered_argument} {}",
                render_obj(parameter_set, &self.environment_stack)?
            );
            let factual_check = check
                .factual_success()
                .ok_or_else(|| format!("by-thm argument check {parameter_index} is not factual"))?;
            if render_fact(&factual_check.fact(), &self.environment_stack)?
                != expected_parameter_fact
                || !factual_check.store.infers.is_empty()
            {
                return Err(format!(
                    "by-thm argument check {parameter_index} changed its parameter obligation"
                ));
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            application_parts.push(rendered_argument);
            application_parts.push(format!("({parameter_proof})"));
        }
        let theorem_application = format!("({})", application_parts.join(" "));

        let mut conclusions = Vec::with_capacity(verification.direct_conclusions.len());
        for (conclusion_index, (conclusion, fact_id)) in verification
            .direct_conclusions
            .iter()
            .zip(conclusion_fact_ids.iter())
            .enumerate()
        {
            let proof = conjunction_projection(
                &theorem_application,
                conclusion_index,
                verification.direct_conclusions.len(),
            )?;
            let proposition = render_fact(conclusion, &self.environment_stack)?;
            conclusions.push(CompiledLitexTheoremInstantiationConclusionProofBody {
                retained_fact_id: *fact_id,
                fact: conclusion.clone(),
                proposition,
                proof_expression: proof,
            });
        }
        Ok(Some(conclusions))
    }

    fn compile_ordinary_fact_goal_proof_body(
        &mut self,
        source_fact: &Fact,
        source_proof_step_count: usize,
        verification: &SuccessVerifyClaimFactResult,
    ) -> Result<Option<CompiledOrdinaryFactGoalProofBody>, String> {
        if verification.fact.to_string() != source_fact.to_string()
            || verification.proof_steps.len() != source_proof_step_count
        {
            return Err("ordinary fact goal Result changed its target or proof-step order".into());
        }
        if !verification.proof_scope.assumption_infers.is_empty()
            || !verification.proof_scope.assumption_components.is_empty()
        {
            return Err("ordinary fact goal retained unexpected local assumptions".into());
        }
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(
                &verification.well_definedness,
                source_fact,
            )?;
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let mut local_proof_lines = Vec::with_capacity(verification.proof_steps.len());
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                local_proof_lines.extend(lines);
            }

            let conclusion = verification
                .conclusion_check
                .factual_success()
                .ok_or_else(|| "ordinary fact goal conclusion is not factual".to_string())?;
            if conclusion.fact().to_string() != source_fact.to_string()
                || !conclusion.store.infers.is_empty()
            {
                return Err(
                    "ordinary fact goal conclusion changed its target or gained effects".into(),
                );
            }
            let Some(conclusion_proof) =
                self.construct_lean_proof_from_direct_fact_result(conclusion)?
            else {
                return Ok(None);
            };
            let proposition = render_fact(source_fact, &self.environment_stack)?;
            Ok(Some(CompiledOrdinaryFactGoalProofBody {
                local_proof_lines,
                proposition,
                conclusion_proof,
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    fn compile_stmt_result_as_local_proof_steps(
        &mut self,
        result: &StmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        if let Some(factual) = result.factual_success() {
            return self
                .compile_fact_stmt_result_as_local_proof_step(factual, proof_step_index)
                .map(|line| line.map(|line| vec![line]));
        }
        if let StmtResult::Success(SuccessStmtResult::By(by_result)) = result {
            let (proofs, effects) = match by_result {
                SuccessByStmtResult::ByCasesStmt(result) => (
                    self.construct_lean_proofs_from_by_cases_stmt_result(result)?,
                    &result.common.infers,
                ),
                SuccessByStmtResult::ByContraStmt(result) => (
                    self.construct_lean_proof_from_by_contra_stmt_result(result)?
                        .map(|proof| vec![proof]),
                    &result.common.infers,
                ),
                _ => return Ok(None),
            };
            let Some(proofs) = proofs else {
                return Ok(None);
            };
            let fact_ids = validate_compiled_fact_proof_effects(
                effects,
                &proofs,
                &self.environment_stack,
                "local by-statement outputs",
            )?;
            let multiple_outputs = proofs.len() > 1;
            let mut lines = Vec::with_capacity(proofs.len());
            for (output_index, (proof, fact_id)) in proofs.into_iter().zip(fact_ids).enumerate() {
                let name = if multiple_outputs {
                    format!("__step{proof_step_index}_{}", output_index + 1)
                } else {
                    format!("__step{proof_step_index}")
                };
                if let Some(fact_id) = fact_id {
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, proof.fact);
                }
                lines.push(format!(
                    "have {name} : {} := by\n  exact {}",
                    proof.proposition, proof.proof_expression
                ));
            }
            return Ok(Some(lines));
        }
        let StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessExistFact(result),
        )) = result
        else {
            return Ok(None);
        };
        let Some(proof_body) =
            self.construct_lean_proof_from_witness_exist_fact_stmt_result(result)?
        else {
            return Ok(None);
        };
        let existential: Fact = result.statement.exist_fact_in_witness.clone().into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &existential,
            "local existential witness effect",
        )?;
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, existential);
        Ok(Some(vec![format!(
            "have {name} : {} := by\n  exact {}",
            proof_body.proposition, proof_body.proof_expression
        )]))
    }

    fn compile_fact_stmt_result_as_local_proof_step(
        &mut self,
        result: &SuccessFactStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<String>, String> {
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("local fact changed between verification and store".into());
        }
        let fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "local proof-step fact has no frozen FactId".to_string())?;
        if result.store.infers.is_empty() {
            let Some(existing) = self.environment_stack.fact_propositions.get(&fact_id) else {
                return Err("local proof-step reused a FactId outside its compiler scope".into());
            };
            if existing.to_string() != source_fact.to_string() {
                return Err("local proof-step reused a FactId for a different proposition".into());
            }
        } else {
            if !result.store.infers.rule_applications.is_empty()
                || result.store.infers.store_fact_outputs.len() != 1
            {
                return Ok(None);
            }
            let stored = &result.store.infers.store_fact_outputs[0];
            if stored.fact_id != Some(fact_id)
                || stored.itself_and_why_itself_is_stored.0.to_string() != source_fact.to_string()
                || !stored.inferred_facts.is_empty()
                || !stored.inferred_fact_ids.is_empty()
            {
                return Err("local proof-step store does not retain its exact FactId".into());
            }
        }
        let Some(proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(None);
        };
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact);
        Ok(Some(format!(
            "have {name} : {proposition} := by\n  exact {proof}"
        )))
    }

    /// Returns `None` when the factual proof family still belongs to the
    /// compatibility migration backlog. A matched typed certificate that is
    /// internally inconsistent is an error, never a fallback.
    fn construct_lean_proof_from_direct_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<Option<String>, String> {
        let source_fact = result.fact();
        match result.proof() {
            SuccessFactProofResult::Fact(citation)
                if citation.fact_transformation.is_none()
                    && citation.checked_function_definition_reduction.is_none()
                    && citation.definition_reduction.is_none() =>
            {
                self.construct_lean_fact_citation_with_equality_transport_from_result(
                    &source_fact,
                    citation.cite_what.as_ref(),
                    citation.source_fact_id,
                    citation.equality_transport.as_ref(),
                )
            }
            SuccessFactProofResult::BuiltinRule(builtin) => {
                if matches!(
                    builtin.evidence,
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        builtin,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) = &builtin.evidence
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule)) =
                    &builtin.evidence
                {
                    return self.construct_lean_real_arithmetic_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence,
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match &builtin.evidence {
                    Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("object-reflexivity evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "object-reflexivity evidence targets a non-equality fact".into()
                            );
                        };
                        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
                            return Err(
                                "object-reflexivity evidence changed its equality endpoints".into(),
                            );
                        }
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        let rendered_object = if result.well_definedness.recursive.is_some() {
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.left,
                            )?
                        } else {
                            render_obj(&equality.left, &self.environment_stack)?
                        };
                        Ok(Some(format!("Litex.Same.refl {rendered_object}")))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("rational-normalization evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "rational-normalization evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if obj_equality_key(&equality.left)
                            != obj_equality_key(&evidence.left_evaluation.expression)
                            || obj_equality_key(&equality.right)
                                != obj_equality_key(&evidence.right_evaluation.expression)
                        {
                            return Err(
                                "rational-normalization evidence changed an equality endpoint"
                                    .into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "rational-normalization evidence retained unequal normal forms"
                                    .into(),
                            );
                        }
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        if result.well_definedness.recursive.is_some() {
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.left,
                            )?;
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.right,
                            )?;
                        } else {
                            render_obj(&equality.left, &self.environment_stack)?;
                            render_obj(&equality.right, &self.environment_stack)?;
                        }
                        Ok(Some(
                            "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                                .into(),
                        ))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "closed-numeric-membership evidence changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "closed-numeric-comparison evidence changed its target".into()
                            );
                        }
                        Ok(Some(render_closed_numeric_comparison_fact(
                            &source_fact,
                            &self.environment_stack,
                        )?))
                    }
                    _ => Ok(None),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            _ => Ok(None),
        }
    }

    /// `Wrap`: cite the exact source FactId, then apply the verifier-retained
    /// equality edges in their recorded order. The Result owns both the
    /// orientation and the equality FactId of every edge; the compiler does
    /// not search the current environment for a proposition-shaped match.
    fn construct_lean_fact_citation_with_equality_transport_from_result(
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
            let equality_fact_id = step.equality_fact_id.ok_or_else(|| {
                format!("equality transport step {step_index} has no equality FactId")
            })?;
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

    /// `Wrap`: compile the one exact source-membership child first and then
    /// apply the fixed standard-set inclusion chain selected by the retained
    /// source and target sets. This consumes the recursive Result directly;
    /// no diagnostic label or compatibility proof IR participates.
    fn construct_lean_standard_set_membership_projection_from_result(
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

    /// `Wrap`: the arithmetic-closure Result owns exactly one conjunction
    /// child Result. The child retains the two ordered operand memberships;
    /// no diagnostic label or rebuilt verifier search participates here.
    fn construct_lean_real_arithmetic_membership_closure_from_result(
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
        Ok(Some(format!(
            "(by\n  have __components := {components_proof}\n  exact Litex.Rules.{theorem} (__components.1) (__components.2))"
        )))
    }

    fn construct_lean_disjunction_introduction_from_result(
        &mut self,
        target: &Fact,
        builtin: &SuccessBuiltinFactProofResult,
    ) -> Result<Option<String>, String> {
        let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) = &builtin.evidence else {
            return Ok(None);
        };
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
        let [selected_result] = builtin.subgoals.as_slice() else {
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
    fn construct_lean_definition_projection_from_result(
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

    fn construct_lean_combined_fact_proof_from_result(
        &mut self,
        target: &Fact,
        combined: &SuccessCombinedFactProofResult,
    ) -> Result<Option<String>, String> {
        let components = conjunction_components(target)?;
        if components.len() != combined.cite_what.len() {
            return Err("combined fact proof changed its component arity".into());
        }
        let mut proofs = Vec::with_capacity(components.len());
        for (component, item) in components.iter().zip(combined.cite_what.iter()) {
            let proof = match item {
                SuccessCombinedFactProofItemResult::Reuse(reuse) => {
                    if reuse.statement.to_string() != component.to_string()
                        || reuse.source.fact().to_string() != component.to_string()
                    {
                        return Err("combined proof reuse changed its component".into());
                    }
                    self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())?
                }
                SuccessCombinedFactProofItemResult::ByFact(citation)
                    if citation.verify_what.to_string() == component.to_string()
                        && citation.fact_transformation.is_none()
                        && citation.definition_reduction.is_none() =>
                {
                    self.construct_lean_fact_citation_with_equality_transport_from_result(
                        component,
                        citation.cite_what.as_ref(),
                        citation.source_fact_id,
                        citation.equality_transport.as_ref(),
                    )?
                }
                _ => None,
            };
            let Some(proof) = proof else {
                return Ok(None);
            };
            proofs.push(proof);
        }
        Ok(Some(right_associated_conjunction_proof(&proofs)?))
    }

    fn construct_lean_proof_from_shared_verify_fact_result(
        &mut self,
        verification: &SuccessVerifyFactResult,
    ) -> Result<Option<String>, String> {
        let source_fact = verification.fact();
        match verification.proof() {
            SuccessFactProofResult::Fact(citation)
                if citation.fact_transformation.is_none()
                    && citation.checked_function_definition_reduction.is_none()
                    && citation.definition_reduction.is_none() =>
            {
                self.construct_lean_fact_citation_with_equality_transport_from_result(
                    &source_fact,
                    citation.cite_what.as_ref(),
                    citation.source_fact_id,
                    citation.equality_transport.as_ref(),
                )
            }
            SuccessFactProofResult::BuiltinRule(builtin) => {
                if matches!(
                    builtin.evidence,
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        builtin,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) = &builtin.evidence
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence,
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match &builtin.evidence {
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
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared closed-numeric-comparison changed its target".into()
                            );
                        }
                        Ok(Some(render_closed_numeric_comparison_fact(
                            &source_fact,
                            &self.environment_stack,
                        )?))
                    }
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
                    _ => Ok(None),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            _ => Ok(None),
        }
    }

    fn compile_stmt_results_in_new_local_environment(
        &mut self,
        results: &[StmtResult],
    ) -> Result<Vec<String>, String> {
        self.environment_stack.push_inherited_environment();
        let outer_declarations = mem::take(&mut self.declarations);
        let outer_fact_name_index = mem::replace(&mut self.next_fact_name_index, 0);
        let outer_sketch_namespace_index = mem::replace(&mut self.next_sketch_namespace_index, 0);

        let compilation = results
            .iter()
            .try_for_each(|result| self.compile_stmt_result_to_lean_source(result));
        let nested_declarations = mem::take(&mut self.declarations);

        self.declarations = outer_declarations;
        self.next_fact_name_index = outer_fact_name_index;
        self.next_sketch_namespace_index = outer_sketch_namespace_index;
        self.environment_stack.pop_local_environment();

        compilation?;
        Ok(nested_declarations)
    }

    fn compile_compatibility_statement_result_to_lean_source(
        &mut self,
        result: &StmtResult,
    ) -> Result<(), String> {
        let statement = LitexToLeanIrBuilder::new()
            .compile_statement(result)
            .map_err(|error| format!("StmtResult-to-Lean compilation failed: {error:?}"))?;
        construct_lean_declarations_for_compatibility_statement_result(
            &statement,
            &mut self.declarations,
            &mut self.next_fact_name_index,
            &mut self.next_sketch_namespace_index,
            &mut self.environment_stack,
        )
    }

    fn finish_lean_source(self) -> Result<String, String> {
        if self.declarations.is_empty() {
            return Err("StmtResultToLeanCompiler requires at least one Lean declaration".into());
        }

        let file_name = Path::new(&self.source_label)
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid source label `{}`", self.source_label))?;
        let stem = Path::new(file_name)
            .file_stem()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid source label `{}`", self.source_label))?;
        let namespace = format!("__Compiler_{}", lean_identifier(stem));
        Ok(format!(
            "-- Generated by StmtResultToLeanCompiler from {file_name}. DO NOT EDIT.\n\
             import Litex\n\n\
             set_option linter.style.nameCheck false\n\n\
             namespace {namespace}\n\n{}\n\n\
             end {namespace}\n",
            self.declarations.join("\n\n")
        ))
    }
}

fn compile_standard_set_nonempty_fact_proof_from_result(
    result: &StmtResult,
    expected_carrier: &Obj,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let success = result
        .factual_success()
        .ok_or_else(|| "object choice nonemptiness child is not a successful fact".to_string())?;
    let target = success.fact();
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = &target else {
        return Err("object choice nonemptiness child changed fact family".into());
    };
    if obj_equality_key(&nonempty.set) != obj_equality_key(expected_carrier)
        || success.store.fact.to_string() != target.to_string()
        || success.store.fact_id.is_some()
        || !success.store.infers.is_empty()
    {
        return Err(
            "object choice nonemptiness child changed its target or verify-only store".into(),
        );
    }
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        return Err("object choice nonemptiness child is not a builtin leaf".into());
    };
    let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = &builtin.evidence else {
        return Err("object choice nonemptiness child has no typed standard-set evidence".into());
    };
    let Obj::StandardSet(target_set) = expected_carrier else {
        return Err("object choice direct compiler currently requires a standard carrier".into());
    };
    if !builtin.subgoals.is_empty()
        || evidence.expected_target.to_string() != target.to_string()
        || evidence.target_set != *target_set
    {
        return Err("standard-set nonempty evidence changed its target or children".into());
    }
    let theorem = match target_set {
        StandardSet::N => "Litex.Rules.naturalNonempty",
        StandardSet::Z => "Litex.Rules.integerNonempty",
        StandardSet::Q => "Litex.Rules.rationalNonempty",
        StandardSet::R => "Litex.Rules.realNonempty",
        StandardSet::C => "Litex.Rules.complexNonempty",
        unsupported => {
            return Err(format!(
                "unsupported direct standard-set nonempty carrier `{unsupported}`"
            ));
        }
    };
    let rendered_target = render_fact(&target, environment_stack)?;
    let rendered_carrier = render_obj(expected_carrier, environment_stack)?;
    if rendered_target != format!("Litex.Set.Nonempty {rendered_carrier}") {
        return Err("standard-set nonempty evidence changed its rendered target".into());
    }
    Ok(theorem.into())
}

fn object_type_fact_for_compiler_definition(
    object: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
    match param_type {
        ParamType::Set(_) => IsSetFact::new(object, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(object, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(object, line_file).into(),
        ParamType::Obj(set) => InFact::new(object, set.clone(), line_file).into(),
    }
}

fn exact_ordered_fact_ids_from_store_results(
    infer_result: &SuccessInferResult,
    expected_facts: &[Fact],
    statement_family: &str,
) -> Result<Vec<FactId>, String> {
    if infer_result.store_fact_outputs.len() != expected_facts.len() {
        return Err(format!(
            "{statement_family} stored {} facts but its Result requires {}",
            infer_result.store_fact_outputs.len(),
            expected_facts.len()
        ));
    }
    infer_result
        .store_fact_outputs
        .iter()
        .zip(expected_facts.iter())
        .enumerate()
        .map(|(index, (stored, expected))| {
            if stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "{statement_family} store {index} changed `{expected}` to `{}`",
                    stored.itself_and_why_itself_is_stored.0
                ));
            }
            stored.fact_id.ok_or_else(|| {
                format!("{statement_family} store {index} for `{expected}` has no FactId")
            })
        })
        .collect()
}

fn equality_transport_has_no_steps(transport: Option<&EqualityTransportEvidence>) -> bool {
    transport.is_none_or(|transport| transport.steps.is_empty())
}

fn atomic_fact_is_logically_negated(fact: &AtomicFact) -> bool {
    matches!(
        fact,
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
    )
}

fn validate_compiled_fact_proof_effects(
    infer_result: &SuccessInferResult,
    proofs: &[CompiledFactProofBody],
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
    result_layer: &str,
) -> Result<Vec<Option<FactId>>, String> {
    if !infer_result.rule_applications.is_empty() {
        return Err(format!(
            "{result_layer} unexpectedly retained typed inference rules"
        ));
    }
    for output in &infer_result.store_fact_outputs {
        if !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty() {
            return Err(format!(
                "{result_layer} retained inferred children beside its direct outputs"
            ));
        }
    }

    let mut output_index = 0;
    let mut fact_ids = Vec::with_capacity(proofs.len());
    for proof in proofs {
        let next_output = infer_result.store_fact_outputs.get(output_index);
        if next_output.is_some_and(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == proof.fact.to_string()
        }) {
            let output = next_output.expect("checked as present");
            fact_ids.push(Some(output.fact_id.ok_or_else(|| {
                format!("{result_layer} store {output_index} has no FactId")
            })?));
            output_index += 1;
            continue;
        }

        let fact_was_already_visible = environment_stack
            .fact_propositions
            .values()
            .any(|visible| visible.to_string() == proof.fact.to_string());
        if !fact_was_already_visible {
            return Err(format!(
                "{result_layer} neither stored `{}` nor reused it from the current compiler environment",
                proof.fact
            ));
        }
        fact_ids.push(None);
    }
    if output_index != infer_result.store_fact_outputs.len() {
        return Err(format!(
            "{result_layer} retained a store output that does not match its ordered facts"
        ));
    }
    Ok(fact_ids)
}

fn validate_single_fact_store_output(
    infer_result: &SuccessInferResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if !infer_result.rule_applications.is_empty() {
        return Err(format!(
            "{result_layer} unexpectedly retained typed inference rules"
        ));
    }
    let [output] = infer_result.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one store output"
        ));
    };
    if output.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string()
        || !output.inferred_facts.is_empty()
        || !output.inferred_fact_ids.is_empty()
    {
        return Err(format!(
            "{result_layer} changed its stored fact or retained inferred children"
        ));
    }
    output
        .fact_id
        .ok_or_else(|| format!("{result_layer} store has no FactId"))
}

fn validate_success_store_fact_result(
    store: &SuccessStoreFactResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if store.fact.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its source fact"));
    }
    let fact_id = store
        .fact_id
        .ok_or_else(|| format!("{result_layer} has no FactId"))?;
    let output_fact_id =
        validate_single_fact_store_output(&store.infers, expected_fact, result_layer)?;
    if output_fact_id != fact_id {
        return Err(format!(
            "{result_layer} store Result and store output disagree on FactId"
        ));
    }
    Ok(fact_id)
}

fn validate_scoped_fact_check_result(
    result: &SuccessFactStmtResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<(), String> {
    if result.store.fact.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its checked fact"));
    }
    if result.store.infers.is_empty() {
        return Ok(());
    }
    let [output] = result.store.infers.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} retained an invalid number of direct store outputs"
        ));
    };
    if output.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its direct store output"));
    }
    if let (Some(result_fact_id), Some(output_fact_id)) = (result.store.fact_id, output.fact_id) {
        if result_fact_id != output_fact_id {
            return Err(format!(
                "{result_layer} store Result and direct output disagree on FactId"
            ));
        }
    }
    Ok(())
}

fn construct_lean_proof_for_compatibility_fact_result_without_storing(
    result: &StmtResult,
    expected_fact: &Fact,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let success = result
        .factual_success()
        .ok_or_else(|| "compatibility proof child is not a successful fact Result".to_string())?;
    if success.fact().to_string() != expected_fact.to_string() {
        return Err(format!(
            "compatibility proof child changed `{expected_fact}` to `{}`",
            success.fact()
        ));
    }
    let (compiled_fact, compiled_well_definedness) = LitexToLeanIrBuilder::new()
        .compile_nested_fact_result_without_requiring_storage(success)
        .map_err(|error| format!("compatibility fact-proof construction failed: {error:?}"))?;
    if compiled_fact.proposition.to_string() != expected_fact.to_string() {
        return Err("compatibility fact proof changed its proposition".into());
    }
    let mut local_environment = environment_stack.clone();
    local_environment.well_definedness = Some(compiled_well_definedness);
    render_proof(&compiled_fact, &local_environment)
}

fn fact_is_supported_by_direct_named_theorem(fact: &Fact) -> bool {
    match fact {
        Fact::AtomicFact(_) => true,
        Fact::ExistFact(existential) => {
            if !existential.is_plain_exist()
                || existential.params_def_with_type().number_of_params() != 1
                || existential.facts().len() != 1
            {
                return false;
            }
            let group = &existential.params_def_with_type().groups[0];
            group.params.len() == 1
                && matches!(group.param_type, ParamType::Obj(_))
                && matches!(
                    existential.facts()[0].from_ref_to_cloned_fact(),
                    Fact::AtomicFact(_)
                )
        }
        _ => false,
    }
}

fn validate_direct_named_theorem_conclusion_well_definedness(
    result: &SuccessVerifyFactWellDefinedProofResult,
    expected_fact: &Fact,
) -> Result<(), String> {
    if matches!(expected_fact, Fact::AtomicFact(_)) {
        return validate_atomic_fact_well_definedness_proof_result(result, expected_fact);
    }
    let Fact::ExistFact(expected_existential) = expected_fact else {
        return Err("direct named theorem received an unsupported conclusion family".into());
    };
    let SuccessVerifyFactWellDefinedProofResult::ExistFact(result) = result else {
        return Err("existential theorem conclusion has no existential WD Result".into());
    };
    if result.statement.to_string() != expected_existential.to_string()
        || result.binder.parameter_groups.len() != 1
        || result.body.len() != 1
    {
        return Err("existential theorem conclusion WD changed its source structure".into());
    }
    let expected_group = &expected_existential.params_def_with_type().groups[0];
    let actual_group = &result.binder.parameter_groups[0];
    if actual_group.group_index != 0
        || actual_group.parameter_type.to_string() != expected_group.param_type.to_string()
        || actual_group.parameters.len() != 1
        || expected_group.params.len() != 1
    {
        return Err("existential theorem conclusion WD changed its binder mapping".into());
    }
    let parameter = &actual_group.parameters[0];
    if parameter.symbol_id != Some(expected_group.params[0].id()) {
        return Err("existential theorem conclusion WD changed its binder SymbolId".into());
    }
    let expected_set = parameter_set(&expected_group.param_type)?;
    validate_object_parameter_premise(
        expected_group.params[0].id(),
        expected_set,
        &parameter.proposition,
    )?;
    validate_atomic_fact_well_definedness_result(
        parameter.well_definedness.as_ref(),
        &parameter.proposition,
    )?;
    validate_single_fact_store_output(
        &parameter.infers,
        &parameter.proposition,
        "existential theorem conclusion binder WD",
    )?;

    let expected_body = expected_existential.facts()[0].from_ref_to_cloned_fact();
    let body = &result.body[0];
    if body.proposition.to_string() != expected_body.to_string() {
        return Err("existential theorem conclusion WD changed its body fact".into());
    }
    validate_atomic_fact_well_definedness_proof_result(
        body.well_definedness.as_ref(),
        &body.proposition,
    )?;
    validate_success_store_fact_result(
        &body.store,
        &body.proposition,
        "existential theorem conclusion body WD",
    )?;
    Ok(())
}

fn validate_atomic_fact_well_definedness_result(
    result: &SuccessVerifyFactWellDefinedResult,
    source_fact: &Fact,
) -> Result<(), String> {
    let Some(recursive) = result.recursive.as_deref() else {
        return Err("atomic fact has no atomic well-definedness result".into());
    };
    validate_atomic_fact_well_definedness_proof_result(recursive, source_fact)
}

fn validate_atomic_fact_well_definedness_proof_result(
    result: &SuccessVerifyFactWellDefinedProofResult,
    source_fact: &Fact,
) -> Result<(), String> {
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) = result else {
        return Err("atomic fact has no atomic well-definedness result".into());
    };
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("atomic fact WD validator received a non-atomic fact".into());
    };
    if atomic.statement.to_string() != source_fact.to_string() {
        return Err("atomic fact WD result changed its statement".into());
    }
    let expected_arguments = source_atomic_fact.args_ref();
    if atomic.predicate.expected_arity != expected_arguments.len()
        || atomic.arguments.len() != expected_arguments.len()
    {
        return Err("atomic fact WD result changed its predicate arity".into());
    }
    let mut visited = HashSet::new();
    for (expected_index, expected_object) in expected_arguments.into_iter().enumerate() {
        let argument = atomic
            .arguments
            .iter()
            .find(|argument| argument.argument_index == expected_index)
            .ok_or_else(|| format!("closed membership WD result lost argument {expected_index}"))?;
        if obj_equality_key(&argument.source_object) != obj_equality_key(expected_object) {
            return Err(format!(
                "closed membership WD argument {expected_index} changed its source object"
            ));
        }
        validate_success_obj_well_defined_result(
            argument.result.as_ref(),
            expected_object,
            &mut visited,
        )?;
    }
    Ok(())
}

fn fact_result_contains_inferred_facts(result: &SuccessFactStmtResult) -> bool {
    !result.store.infers.rule_applications.is_empty()
        || result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
}

fn validate_success_obj_well_defined_result(
    result: &SuccessVerifyObjWellDefinedResult,
    expected_object: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = result as *const SuccessVerifyObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => {
            if obj_equality_key(&direct.object) != obj_equality_key(expected_object) {
                return Err("object WD result changed its checked object".into());
            }
            if let Some(binder) = &direct.steps.binder {
                validate_success_obj_binder_well_defined_result(binder, expected_object, visited)?;
            }
            for child in &direct.steps.children {
                validate_success_obj_well_defined_result(
                    child.result.as_ref(),
                    &child.source_object,
                    visited,
                )?;
            }
            for check in &direct.steps.fact_checks {
                if check.expected_proposition.to_string() != check.verification.fact().to_string() {
                    return Err("object WD fact check changed its verified proposition".into());
                }
            }
            for requirement in &direct.steps.target_requirements {
                if requirement.expected_proposition.to_string()
                    != requirement.verification.fact().to_string()
                {
                    return Err("object WD target requirement changed its proposition".into());
                }
            }
        }
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
            if obj_equality_key(&reuse.object) != obj_equality_key(expected_object) {
                return Err("reused object WD result changed its checked object".into());
            }
            validate_success_obj_well_defined_result(
                reuse.source.as_ref(),
                expected_object,
                visited,
            )?;
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(_) => {
            return Err("object WD result retained an unresolved recursive reference".into());
        }
    }
    Ok(())
}

fn install_object_well_definedness_store_results(
    result: &SuccessVerifyObjWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = result as *const SuccessVerifyObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => {
            for child in &direct.steps.children {
                install_object_well_definedness_store_results(
                    child.result.as_ref(),
                    environment_stack,
                    visited,
                )?;
            }
            for store in &direct.steps.stores {
                let result_set = direct.intrinsic_result_set.as_ref().ok_or_else(|| {
                    format!(
                        "object WD stored `{}` without an intrinsic result set",
                        store.fact
                    )
                })?;
                let expected: Fact = InFact::new(
                    direct.object.clone(),
                    result_set.clone(),
                    store.fact.line_file(),
                )
                .into();
                if store.fact.to_string() != expected.to_string() {
                    return Err(format!(
                        "object WD store changed intrinsic membership `{expected}` to `{}`",
                        store.fact
                    ));
                }
                let fact_id = store.fact_id.ok_or_else(|| {
                    format!("object WD intrinsic-result store `{expected}` has no FactId")
                })?;
                let matching_source_outputs = store
                    .infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| {
                        output.fact_id == Some(fact_id)
                            && output.itself_and_why_itself_is_stored.0.to_string()
                                == expected.to_string()
                    })
                    .count();
                if matching_source_outputs != 1 {
                    return Err(format!(
                        "object WD intrinsic-result store `{expected}` lost its exact source store output"
                    ));
                }
                let rendered_object = render_obj(&direct.object, environment_stack)?;
                let rendered_set = render_obj(result_set, environment_stack)?;
                let proof = format!("Litex.In.own {rendered_set} {rendered_object}");
                if let Some(existing) = environment_stack.fact_propositions.get(&fact_id) {
                    if existing.to_string() != expected.to_string() {
                        return Err(format!(
                            "object WD FactId `{fact_id}` changed from `{existing}` to `{expected}`"
                        ));
                    }
                }
                environment_stack.fact_names.insert(fact_id, proof);
                environment_stack
                    .fact_propositions
                    .insert(fact_id, expected);
            }
            Ok(())
        }
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
            install_object_well_definedness_store_results(
                reuse.source.as_ref(),
                environment_stack,
                visited,
            )
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(_) => Ok(()),
    }
}

fn validate_success_obj_binder_well_defined_result(
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    owner: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match (binder, owner) {
        (SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result), Obj::SetBuilder(_)) => {
            validate_success_obj_well_defined_child(&result.parameter_carrier, visited)?;
        }
        (SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result), Obj::FnSet(_)) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result),
            Obj::AnonymousFn(_),
        ) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
            validate_success_obj_well_defined_child(&result.body, visited)?;
            validate_success_obj_target_requirement(&result.body_membership)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result),
            Obj::Sum(_) | Obj::Product(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            validate_success_iteration_interval_result(&result.interval, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result),
            Obj::SumOfFiniteSet(_) | Obj::ProductOfFiniteSet(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            match &result.mode {
                SuccessVerifyFiniteAggregateModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_set)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => {
                    validate_success_obj_well_defined_child(&result.aggregate_dependency, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Symbolic(_) => {}
            }
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result),
            Obj::Reduce(_) | Obj::FiniteSetReduce(_),
        ) => {
            validate_success_obj_fact_check(&result.seed_membership)?;
            if let Some(laws) = &result.operation_laws {
                validate_success_obj_well_defined_child(&laws.parameter_carrier, visited)?;
                validate_success_obj_fact_check(&laws.associativity)?;
                validate_success_obj_fact_check(&laws.commutativity)?;
            }
            match &result.mode {
                SuccessVerifyReduceModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_range_or_set)?;
                }
                SuccessVerifyReduceModeResult::Interval(result) => {
                    validate_success_iteration_interval_result(&result.interval, visited)?;
                }
                SuccessVerifyReduceModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyReduceModeResult::Symbolic(result) => {
                    if let SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) =
                        &result.coverage
                    {
                        validate_success_obj_fact_check(&result.subset)?;
                    }
                }
            }
        }
        (SuccessVerifyBinderObjectWellDefinedResult::Structure(result), Obj::StructObj(_)) => {
            for argument in &result.header_arguments {
                validate_success_obj_fact_check(&argument.verification)?;
            }
            for domain in &result.header_domains {
                validate_success_obj_fact_check(domain)?;
            }
            for field in &result.fields {
                validate_success_obj_well_defined_child(&field.carrier, visited)?;
            }
        }
        _ => {
            return Err(format!(
                "object `{owner}` retained a well-definedness binder owned by another constructor"
            ));
        }
    }
    Ok(())
}

fn validate_success_iteration_scalar_return_result(
    result: &SuccessVerifyIterationScalarReturnResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    validate_success_obj_fact_check(&result.return_subset)
}

fn validate_success_iteration_interval_result(
    result: &SuccessVerifyIterationIntervalResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    if let Some(body) = &result.body {
        validate_success_obj_well_defined_child(body, visited)?;
    }
    if let Some(body_membership) = &result.body_membership {
        validate_success_obj_target_requirement(body_membership)?;
    }
    match &result.coverage {
        SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(_) => {}
        SuccessVerifyIterationCoverageResult::Enumerated(result) => {
            for check in &result.checks {
                validate_success_obj_fact_check(check)?;
            }
        }
        SuccessVerifyIterationCoverageResult::Endpoint(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
        SuccessVerifyIterationCoverageResult::IntervalSubset(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
    }
    Ok(())
}

fn validate_success_obj_well_defined_children(
    children: &[SuccessVerifyChildObjWellDefinedResult],
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    for child in children {
        validate_success_obj_well_defined_child(child, visited)?;
    }
    Ok(())
}

fn validate_success_obj_well_defined_child(
    child: &SuccessVerifyChildObjWellDefinedResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_result(child.result.as_ref(), &child.source_object, visited)
}

fn validate_success_obj_fact_check(
    check: &SuccessVerifyFactForObjWellDefinedResult,
) -> Result<(), String> {
    if check.expected_proposition.to_string() != check.verification.fact().to_string() {
        return Err("binder WD fact check changed its verified proposition".into());
    }
    Ok(())
}

fn validate_success_obj_target_requirement(
    requirement: &SuccessVerifyObjTargetRequirementResult,
) -> Result<(), String> {
    if requirement.expected_proposition.to_string() != requirement.verification.fact().to_string() {
        return Err("binder WD target requirement changed its verified proposition".into());
    }
    Ok(())
}

fn validate_success_evaluate_obj_result(result: &SuccessEvaluateObjResult) -> Result<(), String> {
    let recomputed = result
        .expression
        .evaluate_to_normalized_decimal_number_with_result()
        .ok_or_else(|| "closed numeric evaluation expression no longer evaluates".to_string())?;
    compare_success_evaluate_obj_results(result, &recomputed)
}

fn compare_success_evaluate_obj_results(
    retained: &SuccessEvaluateObjResult,
    recomputed: &SuccessEvaluateObjResult,
) -> Result<(), String> {
    if obj_equality_key(&retained.expression) != obj_equality_key(&recomputed.expression)
        || retained.value.normalized_value != recomputed.value.normalized_value
    {
        return Err("closed numeric evaluation changed its expression or value".into());
    }
    match (&retained.step, &recomputed.step) {
        (
            SuccessEvaluateObjStepResult::Literal(retained),
            SuccessEvaluateObjStepResult::Literal(recomputed),
        ) if retained.literal.normalized_value == recomputed.literal.normalized_value => Ok(()),
        (
            SuccessEvaluateObjStepResult::Unary(retained),
            SuccessEvaluateObjStepResult::Unary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.argument, &recomputed.argument)
        }
        (
            SuccessEvaluateObjStepResult::Binary(retained),
            SuccessEvaluateObjStepResult::Binary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.left, &recomputed.left)?;
            compare_success_evaluate_obj_results(&retained.right, &recomputed.right)
        }
        (
            SuccessEvaluateObjStepResult::Shape(retained),
            SuccessEvaluateObjStepResult::Shape(recomputed),
        ) if retained.operator == recomputed.operator
            && retained.inputs.len() == recomputed.inputs.len()
            && retained.evaluated_children.len() == recomputed.evaluated_children.len() =>
        {
            for (retained_input, recomputed_input) in
                retained.inputs.iter().zip(recomputed.inputs.iter())
            {
                if obj_equality_key(retained_input) != obj_equality_key(recomputed_input) {
                    return Err("closed numeric shape evaluation changed an input".into());
                }
            }
            for (retained_child, recomputed_child) in retained
                .evaluated_children
                .iter()
                .zip(recomputed.evaluated_children.iter())
            {
                compare_success_evaluate_obj_results(retained_child, recomputed_child)?;
            }
            Ok(())
        }
        _ => Err("closed numeric evaluation changed its recursive operation tree".into()),
    }
}

fn construct_lean_declarations_for_compatibility_statement_result(
    statement: &LitexToLeanStatementIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    sketch_namespace_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    match statement {
        LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::SketchStmt(sketch)) => {
            crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                &sketch.block.well_definedness,
            )?;
            let mut nested_declarations = Vec::new();
            let mut nested_fact_index = 0;
            let mut nested_sketch_namespace_index = 0;
            let mut nested_context = context.clone();
            for step in &sketch.block.steps {
                construct_lean_declarations_for_compatibility_statement_result(
                    step,
                    &mut nested_declarations,
                    &mut nested_fact_index,
                    &mut nested_sketch_namespace_index,
                    &mut nested_context,
                )?;
            }
            *sketch_namespace_index += 1;
            let namespace = format!("__Sketch{:02}", sketch_namespace_index);
            declarations.push(format!(
                "namespace {namespace}\n\n{}\n\nend {namespace}",
                nested_declarations.join("\n\n")
            ));
        }
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(
            definition,
        )) => construct_lean_declarations_for_compatibility_have_object_equal_result(
            definition,
            declarations,
            fact_index,
            context,
        )?,
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::LetObjStmt(definition)) => {
            construct_lean_declarations_for_compatibility_let_object_result(
                definition,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(
            statement,
        )) => construct_lean_declarations_for_compatibility_object_choices_result(
            statement,
            declarations,
            fact_index,
            context,
        )?,
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveFnEqualStmt(
            definition,
        )) => construct_lean_declarations_for_compatibility_named_function_result(
            definition,
            declarations,
            fact_index,
            context,
        )?,
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveTupleStmt(definition)) => {
            construct_lean_declarations_for_compatibility_indexed_tuple_result(
                definition,
                declarations,
                fact_index,
                context,
            )?
        }
        LitexToLeanStatementIr::DefPredicateStmt(LitexToLeanDefPredicateStmtIr::DefPropStmt(_)) => {
            return Err(
                "concrete `prop` must be compiled directly from SuccessDefPropStmtResult".into(),
            );
        }
        LitexToLeanStatementIr::DefPredicateStmt(
            LitexToLeanDefPredicateStmtIr::DefAbstractPropStmt(definition),
        ) => construct_lean_declaration_for_abstract_predicate_definition(
            definition,
            declarations,
            context,
        )?,
        LitexToLeanStatementIr::UnsafeStmt(LitexToLeanUnsafeStmtIr::TrustStmt(statement)) => {
            construct_lean_declarations_for_compatibility_trust_result(
                statement,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::DefThmStmt(theorem) => {
            crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                &theorem.well_definedness,
            )?;
            let theorem_name = lean_identifier(&theorem.name);
            let proof_steps = theorem
                .proof_steps
                .iter()
                .map(|step| step.statement.clone())
                .collect::<Vec<_>>();
            declarations.push(construct_lean_declaration_for_forall_fact(
                &theorem.theorem,
                &theorem.well_definedness,
                *fact_index,
                &format!("theorem {theorem_name}"),
                &proof_steps,
                context,
            )?);
            if let Some(fact_id) = theorem.theorem.stored_fact_id() {
                context.fact_names.insert(fact_id, theorem_name);
                context
                    .fact_propositions
                    .insert(fact_id, theorem.theorem.proposition.clone());
            }
            *fact_index += 1;
            construct_lean_declarations_for_stored_fact_effects(
                theorem
                    .stored_projections
                    .iter()
                    .chain(theorem.inferred_facts.iter())
                    .collect(),
                &theorem.well_definedness,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ClaimStmt(claim)) => {
            construct_lean_declaration_for_compatibility_claim_result(
                claim,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ExampleStmt(example)) => {
            construct_lean_declaration_for_compatibility_example_result(
                example,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::Fact(fact) => {
            construct_lean_declarations_for_compatibility_fact_result(
                fact,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(statement)) => {
            construct_lean_declarations_for_stored_fact_effects(
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(statement)) => {
            construct_lean_declarations_for_stored_fact_effects(
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(statement)) => {
            construct_lean_declarations_for_stored_fact_effects(
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(statement)) => {
            construct_lean_declarations_for_stored_fact_effects(
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(
            statement,
        )) => {
            construct_lean_declarations_for_existential_elimination(
                &statement.source,
                &statement.witnesses,
                &statement.projections,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::ObtainObjFromAtomicFact(
            statement,
        )) => {
            construct_lean_declarations_for_existential_elimination(
                &statement.source,
                &statement.witnesses,
                &statement.projections,
                declarations,
                fact_index,
                context,
            )?;
        }
        LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjByExistFactsStmt(
            statement,
        )) => {
            construct_lean_declarations_for_existential_elimination(
                &statement.source,
                &statement.witnesses,
                &statement.projections,
                declarations,
                fact_index,
                context,
            )?;
        }
        other => {
            return Err(format!(
                "unsupported compiler statement outside the current fact/set slice: {other:?}"
            ));
        }
    }
    Ok(())
}

fn construct_lean_declarations_for_compatibility_fact_result(
    fact: &LitexToLeanFactStatementIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let mut facts = Vec::new();
    if fact.stored_projections.is_empty() || fact.source.stored_fact_id().is_some() {
        facts.push(&fact.source);
    }
    let mut projections = fact.stored_projections.iter().collect::<Vec<_>>();
    if let Fact::ForallFact(source_forall) = &fact.source.proposition {
        projections.sort_by_key(|projection| {
            let Fact::ForallFact(projected) = &projection.proposition else {
                return usize::MAX;
            };
            let Some(projected_conclusion) = projected.then_facts.first() else {
                return usize::MAX;
            };
            source_forall
                .then_facts
                .iter()
                .position(|source_conclusion| {
                    source_conclusion.clone().to_fact().to_string()
                        == projected_conclusion.clone().to_fact().to_string()
                })
                .unwrap_or(usize::MAX)
        });
    }
    facts.extend(projections);
    facts.extend(fact.inferred_facts.iter());
    construct_lean_declarations_for_stored_fact_effects(
        facts,
        &fact.well_definedness,
        declarations,
        fact_index,
        context,
    )
}

fn construct_lean_declarations_for_stored_fact_effects(
    facts: Vec<&LitexToLeanFactIr>,
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(well_definedness)?;
    let mut seen_fact_ids = HashMap::new();
    for fact in facts {
        if let Some(fact_id) = fact.stored_fact_id() {
            if let Some(previous) = seen_fact_ids.insert(fact_id, fact.proposition.to_string()) {
                if previous != fact.proposition.to_string() {
                    return Err(format!(
                        "FactId `{fact_id}` changed proposition inside one statement emission"
                    ));
                }
                continue;
            }
            if let Some(previous) = context.fact_propositions.get(&fact_id) {
                let same = previous.to_string() == fact.proposition.to_string()
                    || match (previous, &fact.proposition) {
                        (Fact::ForallFact(previous), Fact::ForallFact(current)) => {
                            render_forall_fact_type(previous, context)?
                                == render_forall_fact_type(current, context)?
                        }
                        _ => false,
                    };
                if !same {
                    return Err(format!(
                        "FactId `{fact_id}` was reused for `{previous}` and `{}`",
                        fact.proposition
                    ));
                }
            }
        }
        let theorem_name = format!("__fact{fact_index}");
        declarations.push(construct_lean_declaration_for_stored_fact(
            fact,
            well_definedness,
            *fact_index,
            context,
        )?);
        if let Some(fact_id) = fact.stored_fact_id() {
            context.fact_names.insert(fact_id, theorem_name.clone());
            context
                .fact_propositions
                .insert(fact_id, fact.proposition.clone());
        }
        register_forall_conclusion_bindings(fact, &theorem_name, context)?;
        *fact_index += 1;
    }
    Ok(())
}

fn register_forall_conclusion_bindings(
    fact: &LitexToLeanFactIr,
    theorem_name: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let (
        Fact::ForallFact(forall),
        LitexToLeanFactProofIr::ForallIntroduction {
            parameter_premises,
            premises,
            conclusions,
            ..
        },
    ) = (&fact.proposition, &fact.proof)
    else {
        return Ok(());
    };
    for (conclusion_index, conclusion) in conclusions.iter().enumerate() {
        let Some(fact_id) = conclusion.stored_fact_id() else {
            continue;
        };
        if let Some(previous) = context.fact_propositions.get(&fact_id) {
            if previous.to_string() != conclusion.proposition.to_string() {
                return Err(format!(
                    "forall conclusion FactId `{fact_id}` changed from `{previous}` to `{}`",
                    conclusion.proposition
                ));
            }
        }
        context
            .fact_propositions
            .insert(fact_id, conclusion.proposition.clone());
        context.forall_conclusion_bindings.insert(
            fact_id,
            ForallConclusionBinding {
                theorem_name: theorem_name.to_string(),
                forall: forall.clone(),
                parameter_premises: parameter_premises.clone(),
                premises: premises.clone(),
                conclusion_index,
                conclusion_count: conclusions.len(),
            },
        );
    }
    Ok(())
}

fn construct_lean_declarations_for_compatibility_let_object_result(
    definition: &LitexToLeanLetObjStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &definition.well_definedness,
    )?;
    let name = lean_identifier(&definition.name);
    let value = render_native_object_ir(&definition.value, context)?;
    if context
        .symbol_names
        .insert(definition.symbol_id, name.clone())
        .is_some()
    {
        return Err(format!(
            "duplicate compiler symbol identity for `{}`",
            definition.name
        ));
    }
    declarations.push(format!("noncomputable def {name} := {value}"));
    construct_lean_declarations_for_stored_fact_effects(
        std::iter::once(&definition.defining_equality)
            .chain(definition.inferred_facts.iter())
            .collect(),
        &definition.well_definedness,
        declarations,
        fact_index,
        context,
    )
}

fn construct_lean_declaration_for_abstract_predicate_definition(
    definition: &LitexToLeanDefAbstractPropStmtIr,
    declarations: &mut Vec<String>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    construct_lean_source_parts_for_abstract_predicate_definition(
        &definition.name,
        &definition.params,
        declarations,
        context,
    )
}

fn construct_lean_source_parts_for_abstract_predicate_definition(
    source_name: &str,
    parameter_names: &[String],
    declarations: &mut Vec<String>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if context.predicate_bindings.contains_key(source_name) {
        return Err(format!(
            "duplicate compiler predicate definition `{}`",
            source_name
        ));
    }
    let name = lean_identifier(source_name);
    let mut universe_names = Vec::with_capacity(parameter_names.len());
    let mut binders = Vec::with_capacity(parameter_names.len() * 2);
    for (index, parameter_name) in parameter_names.iter().enumerate() {
        let suffix = index + 1;
        let universe = format!("u__{name}_{suffix}");
        let carrier = format!("__abstract_carrier{suffix}");
        universe_names.push(universe.clone());
        binders.push(format!("{{{carrier} : Type {universe}}}"));
        binders.push(format!("({} : {carrier})", lean_identifier(parameter_name)));
    }
    let universe_declaration = if universe_names.is_empty() {
        String::new()
    } else {
        format!("universe {}\n", universe_names.join(" "))
    };
    let binder_suffix = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    declarations.push(format!(
        "{universe_declaration}axiom {name}{binder_suffix} : Prop"
    ));
    context.predicate_bindings.insert(
        source_name.to_string(),
        PredicateBinding {
            lean_name: name,
            parameter_count: parameter_names.len(),
            requirement_count: 0,
            clause_count: 0,
            definition: None,
        },
    );
    Ok(())
}

fn construct_lean_declarations_for_compatibility_trust_result(
    statement: &LitexToLeanTrustStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if statement.facts.is_empty() {
        return Err("explicit source `trust` retained no propositions".into());
    }
    for fact in &statement.facts {
        if !matches!(fact.proof, LitexToLeanFactProofIr::Trusted) {
            return Err("explicit source `trust` lost its Trusted IR marker".into());
        }
        let fact_id = fact.stored_fact_id().ok_or_else(|| {
            "explicit source `trust` requires one stored source FactId".to_string()
        })?;
        let name = format!("__fact{fact_index}");
        let proposition = match &fact.proposition {
            Fact::ForallFact(forall) => render_forall_fact_type(forall, context)?,
            _ => render_fact(&fact.proposition, context)?,
        };
        declarations.push(format!("axiom {name} : {proposition}"));
        context.fact_names.insert(fact_id, name);
        context
            .fact_propositions
            .insert(fact_id, fact.proposition.clone());
        *fact_index += 1;
    }
    for inferred in &statement.inferred_facts {
        if matches!(inferred.proof, LitexToLeanFactProofIr::Trusted) {
            return Err("a trust-inferred fact may not create another Lean axiom".into());
        }
        let name = format!("__fact{fact_index}");
        let proposition = render_fact(&inferred.proposition, context)?;
        let proof = render_proof(inferred, context)?;
        declarations.push(format!(
            "theorem {name} : {proposition} := by\n  exact {proof}"
        ));
        if let Some(fact_id) = inferred.stored_fact_id() {
            context.fact_names.insert(fact_id, name);
            context
                .fact_propositions
                .insert(fact_id, inferred.proposition.clone());
        }
        *fact_index += 1;
    }
    Ok(())
}

fn construct_lean_declarations_for_compatibility_object_choices_result(
    statement: &LitexToLeanHaveObjInNonemptySetOrParamTypeStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if statement.choices.is_empty() {
        return Err("compiler object choice retained no selected objects".into());
    }
    for choice in &statement.choices {
        let name = lean_identifier(&choice.name);
        let carrier = render_set_ir(&choice.carrier, context)?;
        let nonempty_type = render_fact(&choice.nonempty_proof.proposition, context)?;
        let expected_nonempty = format!("Litex.Set.Nonempty {carrier}");
        if nonempty_type != expected_nonempty {
            return Err(format!(
                "object choice expected `{expected_nonempty}`, retained `{nonempty_type}`"
            ));
        }
        let nonempty_proof = render_proof(&choice.nonempty_proof, context)?;
        if context
            .symbol_names
            .insert(choice.symbol_id, name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{}`",
                choice.name
            ));
        }
        declarations.push(format!(
            "noncomputable def {name} : {carrier}.Carrier :=\n  Classical.choice ({nonempty_proof})"
        ));

        let proposition = render_fact(&choice.membership.proposition, context)?;
        let proof = render_proof(&choice.membership, context)?;
        let theorem_name = format!("__fact{fact_index}");
        declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        if let Some(fact_id) = choice.membership.stored_fact_id() {
            context.fact_names.insert(fact_id, theorem_name);
            context
                .fact_propositions
                .insert(fact_id, choice.membership.proposition.clone());
        }
        *fact_index += 1;
    }
    Ok(())
}

fn construct_lean_declarations_for_compatibility_indexed_tuple_result(
    definition: &LitexToLeanHaveTupleStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let LitexToLeanObjectIr::Number { normalized_value } = &definition.dimension else {
        return Err("indexed tuple dimension must be a closed natural numeral".into());
    };
    let dimension = normalized_value
        .parse::<usize>()
        .map_err(|_| "indexed tuple dimension is not a machine natural".to_string())?;
    if dimension < 2 || definition.dimension_checks.len() != 2 {
        return Err("indexed tuple requires its positive-dimension and at-least-two checks".into());
    }
    if !indexed_tuple_value_is_complex(&definition.value, definition.index_symbol_id) {
        return Err(
            "indexed tuple coordinate expression has no reviewed uniform complex carrier".into(),
        );
    }

    let name = lean_identifier(&definition.name);
    let mut body_context = context.clone();
    body_context
        .symbol_names
        .insert(definition.index_symbol_id, "__index".into());
    body_context.numeric_representations.insert(
        definition.index_symbol_id,
        "(((__index.val : ℤ) : ℂ))".into(),
    );
    let value = render_numeric_object_ir(&definition.value, &body_context)?;

    for (check_index, check) in definition.dimension_checks.iter().enumerate() {
        let proposition = render_fact(&check.proposition, context)?;
        let proof = render_proof(check, context)?;
        declarations.push(format!(
            "theorem __{name}_dimension_check{} : {proposition} := by\n  exact {proof}",
            check_index + 1
        ));
    }
    declarations.push(format!(
        "noncomputable def {name} : Litex.IndexedTuple {dimension} ℂ :=\n  ⟨fun __index => {value}⟩"
    ));
    if context
        .symbol_names
        .insert(definition.symbol_id, name.clone())
        .is_some()
    {
        return Err(format!(
            "duplicate compiler symbol identity for indexed tuple `{}`",
            definition.name
        ));
    }
    context
        .indexed_tuple_bindings
        .insert(definition.symbol_id, IndexedTupleBinding { dimension });

    let mut is_tuple = None;
    let mut dimension_fact = None;
    let mut coordinate = None;
    for fact in &definition.stored_facts {
        let slot = match fact.role {
            LitexToLeanStoredTupleFactRoleIr::IsTuple => &mut is_tuple,
            LitexToLeanStoredTupleFactRoleIr::Dimension => &mut dimension_fact,
            LitexToLeanStoredTupleFactRoleIr::Coordinate => &mut coordinate,
        };
        if slot.replace(fact).is_some() {
            return Err("indexed tuple retained a duplicate stored-effect role".into());
        }
    }
    let (Some(is_tuple), Some(dimension_fact), Some(coordinate)) =
        (is_tuple, dimension_fact, coordinate)
    else {
        return Err("indexed tuple requires three ordered stored-effect roles".into());
    };

    let Fact::AtomicFact(AtomicFact::IsTupleFact(tuple_fact)) = &is_tuple.proposition else {
        return Err("indexed tuple IsTuple effect changed proposition shape".into());
    };
    if !object_is_symbol(&tuple_fact.set, definition.symbol_id) {
        return Err("indexed tuple IsTuple effect changed its declared object".into());
    }
    let theorem_name = format!("__fact{fact_index}");
    declarations.push(format!(
        "theorem {theorem_name} : {} := by\n  exact ⟨inferInstance⟩",
        render_fact(&is_tuple.proposition, context)?
    ));
    context.fact_names.insert(is_tuple.fact_id, theorem_name);
    context
        .fact_propositions
        .insert(is_tuple.fact_id, is_tuple.proposition.clone());
    *fact_index += 1;

    let (left, right) = equality_parts(&dimension_fact.proposition)?;
    let Obj::TupleDim(tuple_dimension) = left else {
        return Err("indexed tuple dimension effect lost tuple_dim".into());
    };
    if !object_is_symbol(tuple_dimension.arg.as_ref(), definition.symbol_id)
        || LitexToLeanObjectIr::lower(right)? != definition.dimension
    {
        return Err("indexed tuple dimension effect changed its object or dimension".into());
    }
    let theorem_name = format!("__fact{fact_index}");
    declarations.push(format!(
        "theorem {theorem_name} : {} := by\n  exact Litex.Same.ofEq (by rfl)",
        render_fact(&dimension_fact.proposition, context)?
    ));
    context
        .fact_names
        .insert(dimension_fact.fact_id, theorem_name);
    context
        .fact_propositions
        .insert(dimension_fact.fact_id, dimension_fact.proposition.clone());
    *fact_index += 1;

    construct_lean_declaration_for_indexed_tuple_coordinate(
        definition,
        coordinate,
        declarations,
        fact_index,
        context,
    )
}

fn construct_lean_declaration_for_indexed_tuple_coordinate(
    definition: &LitexToLeanHaveTupleStmtIr,
    coordinate: &LitexToLeanStoredTupleFactIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let Fact::ForallFact(forall) = &coordinate.proposition else {
        return Err("indexed tuple coordinate effect is not a forall".into());
    };
    let parameters = forall
        .params_def_with_type
        .collect_param_bindings_with_types();
    let [(binding, param_type)] = parameters.as_slice() else {
        return Err("indexed tuple coordinate effect changed its one-index binder".into());
    };
    if !forall.dom_facts.is_empty() || forall.then_facts.len() != 1 {
        return Err(
            "indexed tuple coordinate effect changed its domain or conclusion arity".into(),
        );
    }
    let Obj::ClosedRange(range) = parameter_set(param_type)? else {
        return Err("indexed tuple coordinate binder is not the checked closed range".into());
    };
    let expected_start = LitexToLeanObjectIr::Number {
        normalized_value: "1".into(),
    };
    if LitexToLeanObjectIr::lower(range.start.as_ref())? != expected_start
        || LitexToLeanObjectIr::lower(range.end.as_ref())? != definition.dimension
    {
        return Err("indexed tuple coordinate range changed its one-based dimension".into());
    }

    let index = "__tuple_index";
    let membership = "__tuple_index_in";
    let exact_index = format!("(Litex.In.rep {index} {membership})");
    let mut nested = context.clone();
    nested.symbol_names.insert(binding.id(), index.into());
    nested
        .exact_tuple_indices
        .insert(binding.id(), exact_index.clone());
    nested
        .numeric_representations
        .insert(binding.id(), format!("((({exact_index}).val : ℤ) : ℂ)"));
    let conclusion = forall.then_facts[0].clone().to_fact();
    let rendered_conclusion = render_fact(&conclusion, &nested)?;
    let range = format!(
        "(Litex.closedRange (1 : ℤ) ({} : ℤ))",
        match &definition.dimension {
            LitexToLeanObjectIr::Number { normalized_value } => normalized_value,
            _ => unreachable!("dimension was validated before coordinate emission"),
        }
    );
    let theorem_name = format!("__fact{fact_index}");
    declarations.push(format!(
        "theorem {theorem_name} :\n    ∀ {{__tuple_index_carrier : Type}} ({index} : __tuple_index_carrier) ({membership} : Litex.In {index} {range}),\n      {rendered_conclusion} := by\n  intro __tuple_index_carrier {index} {membership}\n  exact Litex.Same.ofEq (by rfl)"
    ));
    context.fact_names.insert(coordinate.fact_id, theorem_name);
    context
        .fact_propositions
        .insert(coordinate.fact_id, coordinate.proposition.clone());
    *fact_index += 1;
    Ok(())
}

fn object_is_symbol(object: &Obj, symbol_id: SymbolId) -> bool {
    matches!(object, Obj::Atom(atom) if atom.symbol_ref().is_some_and(|symbol| symbol.id() == symbol_id))
}

fn indexed_tuple_value_is_complex(object: &LitexToLeanObjectIr, index: SymbolId) -> bool {
    match object {
        LitexToLeanObjectIr::Number { .. } | LitexToLeanObjectIr::Constant(_) => true,
        LitexToLeanObjectIr::Symbol { symbol_id, .. } => *symbol_id == index,
        LitexToLeanObjectIr::BuiltinApp {
            operator,
            arguments,
            ..
        } if matches!(
            operator,
            LitexToLeanBuiltinObjectOperatorIr::Add
                | LitexToLeanBuiltinObjectOperatorIr::Sub
                | LitexToLeanBuiltinObjectOperatorIr::Mul
                | LitexToLeanBuiltinObjectOperatorIr::Div
        ) =>
        {
            arguments
                .iter()
                .all(|argument| indexed_tuple_value_is_complex(argument, index))
        }
        _ => false,
    }
}

fn construct_lean_declarations_for_compatibility_named_function_result(
    definition: &LitexToLeanHaveFnEqualStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &definition.well_definedness,
    )?;
    validate_function_type(&definition.function)?;
    if definition.parameter_premises.len() != definition.function.parameters.len() {
        return Err(
            "compiler named-function construction changed its parameter-membership premise count"
                .into(),
        );
    }
    if definition.domain_premises.len() != definition.function.domain_facts.len() {
        return Err(
            "compiler named-function construction changed its domain-clause premise count".into(),
        );
    }
    let mut local = context.clone();
    for (index, (parameter, premise)) in definition
        .function
        .parameters
        .iter()
        .zip(definition.parameter_premises.iter())
        .enumerate()
    {
        let suffix = if !function_uses_telescope(&definition.function) {
            String::new()
        } else {
            (index + 1).to_string()
        };
        local
            .symbol_names
            .insert(parameter.symbol_id, format!("__arg{suffix}"));
        local
            .fact_names
            .insert(premise.fact_id, format!("__arg{suffix}_in"));
        local
            .fact_propositions
            .insert(premise.fact_id, premise.fact.clone());
        let argument = format!("__arg{suffix}");
        let membership = format!("__arg{suffix}_in");
        if let Some(real) = membership_real_value(&parameter.set, &argument, &membership) {
            local.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &membership)
        {
            local
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) = membership_numeric_proof(&parameter.set, &argument, &membership) {
            local
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
    }
    for (index, domain) in definition.domain_premises.iter().enumerate() {
        let selector = conjunction_selector(index, definition.domain_premises.len())?;
        local.fact_names.insert(
            domain.fact_id,
            if definition.domain_premises.len() == 1 {
                "__arg_domain".into()
            } else {
                format!("__arg_domain{selector}")
            },
        );
        local
            .fact_propositions
            .insert(domain.fact_id, domain.fact.clone());
    }
    local.well_definedness = Some(definition.well_definedness.clone());

    let name = lean_identifier(&definition.name);
    // A telescope carrier starts with implicit heterogeneous carrier binders.
    // Lean otherwise eagerly inserts the first implicit argument when the
    // named function is used as a value, silently turning the whole source
    // layer into a partially applied function. `@name` preserves the exact
    // one-layer carrier object.
    let function_value_name = if !function_uses_telescope(&definition.function) {
        name.clone()
    } else {
        format!("(@{name})")
    };
    if context
        .symbol_names
        .insert(definition.symbol_id, function_value_name.clone())
        .is_some()
    {
        return Err(format!(
            "duplicate compiler symbol identity for `{}`",
            definition.name
        ));
    }
    let (value, uses_native_real_body) = render_named_function_value(definition, &local)?;
    let function_type = render_function_type(&definition.function, context)?;
    let function_set = render_function_set(&definition.function, context)?;
    declarations.push(format!(
        "noncomputable def {name} : {function_type} :=\n  {value}"
    ));

    let membership_proposition = render_fact(&definition.membership.proposition, context)?;
    let membership_name = format!("__fact{fact_index}");
    declarations.push(format!(
        "theorem {membership_name} : {membership_proposition} := by\n  exact Litex.In.own {function_set} {function_value_name}"
    ));
    context
        .fact_names
        .insert(definition.membership.fact_id, membership_name.clone());
    context.fact_propositions.insert(
        definition.membership.fact_id,
        definition.membership.proposition.clone(),
    );
    context.function_bindings.insert(
        definition.membership.fact_id,
        FunctionBinding {
            symbol_id: definition.symbol_id,
            function: definition.function.clone(),
            membership_proof_name: membership_name,
            direct: true,
        },
    );
    *fact_index += 1;

    let equality_proposition =
        format!("Litex.Same {function_value_name} ({value} : {function_type})");
    let equality_name = format!("__fact{fact_index}");
    declarations.push(format!(
        "theorem {equality_name} : {equality_proposition} := by\n  unfold {name}\n  exact Litex.Same.refl ({value} : {function_type})"
    ));
    context
        .fact_names
        .insert(definition.defining_equality.fact_id, equality_name);
    context.fact_propositions.insert(
        definition.defining_equality.fact_id,
        definition.defining_equality.proposition.clone(),
    );
    context.named_function_definitions.insert(
        definition.defining_equality.fact_id,
        NamedFunctionDefinitionBinding {
            symbol_id: definition.symbol_id,
            name,
            function: definition.function.clone(),
            source_body: definition.source_body.clone(),
            body: definition.body.clone(),
            uses_native_real_body,
            parameter_premises: definition.parameter_premises.clone(),
            domain_premises: definition.domain_premises.clone(),
            compatibility_return_selection: Some(
                CompatibilityNamedFunctionReturnSelectionBinding {
                    inferred_premises: definition.inferred_premises.clone(),
                    return_check: definition.return_check.clone(),
                },
            ),
            well_definedness: definition.well_definedness.clone(),
        },
    );
    *fact_index += 1;
    Ok(())
}

fn construct_lean_declarations_for_existential_elimination(
    source: &LitexToLeanFactIr,
    witnesses: &[LitexToLeanExistentialWitnessIr],
    projections: &[LitexToLeanFactIr],
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let Fact::ExistFact(existential) = &source.proposition else {
        return Err("existential elimination retained a non-existential source".into());
    };
    if !existential.is_plain_exist()
        || existential.params_def_with_type().number_of_params() != 1
        || existential.facts().len() != 1
        || witnesses.len() != 1
        || projections.len() != 2
    {
        return Err(
            "compiler existential elimination supports one positive witness and one body fact"
                .into(),
        );
    }
    let group = &existential.params_def_with_type().groups[0];
    if group.params.len() != 1 {
        return Err("existential elimination requires one singleton parameter group".into());
    }
    let LitexToLeanParameterTypeIr::MemberOf { set } = &witnesses[0].param_type else {
        return Err("existential elimination currently requires a membership witness".into());
    };
    let source_proof = render_proof(source, context)?;
    let witness_name = lean_identifier(&witnesses[0].name);
    let source_set = parameter_set(&group.param_type)?;
    if LitexToLeanObjectIr::lower(source_set)? != *set {
        return Err("existential witness changed its retained source set".into());
    }
    let dynamic_carrier = set_requires_heterogeneous_carrier(source_set);
    let function_carrier = matches!(source_set, Obj::FnSet(_));
    let carrier_name = format!("__carrier_{witness_name}");
    let specification = if dynamic_carrier || function_carrier {
        declarations.push(format!(
            "noncomputable def {carrier_name} : {} := Classical.choose ({source_proof})",
            if function_carrier { "Type 1" } else { "Type" }
        ));
        declarations.push(format!(
            "noncomputable def {witness_name} : {carrier_name} :=\n  Classical.choose (Classical.choose_spec ({source_proof}))"
        ));
        format!("Classical.choose_spec (Classical.choose_spec ({source_proof}))")
    } else {
        declarations.push(format!(
            "noncomputable def {witness_name} : ℂ := Classical.choose ({source_proof})"
        ));
        format!("Classical.choose_spec ({source_proof})")
    };
    context
        .symbol_names
        .insert(witnesses[0].symbol_id, witness_name.clone());
    context
        .symbol_names
        .insert(group.params[0].id(), witness_name.clone());
    context
        .existential_names
        .insert(group.params[0].name().to_string(), witness_name.clone());

    let expected_requirement = format!(
        "Litex.In {witness_name} {}",
        render_obj(source_set, context)?
    );
    let expected_body = render_fact(&existential.facts()[0].from_ref_to_cloned_fact(), context)?;
    let mut saw_requirement = false;
    let mut saw_body = false;
    for projection in projections {
        let LitexToLeanFactProofIr::ExistentialElimination { role } = &projection.proof else {
            return Err("existential projection has malformed proof evidence".into());
        };
        let (expected, selector) = match role {
            LitexToLeanExistentialProjectionRoleIr::ParameterType { witness_index: 0 } => {
                saw_requirement = true;
                (&expected_requirement, ".1")
            }
            LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index: 0 } => {
                saw_body = true;
                (&expected_body, ".2")
            }
            _ => return Err("existential projection role is outside the one-witness slice".into()),
        };
        let proposition = render_fact(&projection.proposition, context)?;
        if &proposition != expected {
            return Err("existential projection does not match its retained role".into());
        }
        let theorem_name = format!("__fact{fact_index}");
        let unfold = if dynamic_carrier || function_carrier {
            format!("{witness_name} {carrier_name}")
        } else {
            witness_name.clone()
        };
        declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  unfold {unfold}\n  exact ({specification}){selector}"
        ));
        if let Some(fact_id) = projection.stored_fact_id() {
            context.fact_names.insert(fact_id, theorem_name);
            context
                .fact_propositions
                .insert(fact_id, projection.proposition.clone());
        }
        *fact_index += 1;
    }
    if !saw_requirement || !saw_body {
        return Err("existential elimination lost a required projection".into());
    }
    Ok(())
}

fn construct_lean_declaration_for_compatibility_claim_result(
    claim: &LitexToLeanClaimStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &claim.well_definedness,
    )?;
    if !claim.inferred_facts.is_empty() {
        return Err("compiler claim MVP does not yet emit inferred outer facts".into());
    }
    let mut nested = context.clone();
    let mut local_index = 0;
    let mut lines =
        render_local_proof_block(&claim.block, &mut nested, "__step", &mut local_index)?;
    let proposition = render_fact(&claim.target.proposition, &nested)?;
    lines.push(format!("exact {}", render_proof(&claim.target, &nested)?));
    declarations.push(format!(
        "theorem __fact{fact_index} : {proposition} := by\n{}",
        indent_lines(&lines.join("\n"), 2)
    ));
    if let Some(fact_id) = claim.target.stored_fact_id() {
        context
            .fact_names
            .insert(fact_id, format!("__fact{fact_index}"));
        context
            .fact_propositions
            .insert(fact_id, claim.target.proposition.clone());
    }
    *fact_index += 1;
    Ok(())
}

fn construct_lean_declaration_for_compatibility_example_result(
    example: &LitexToLeanExampleStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &example.well_definedness,
    )?;
    if matches!(
        (&example.target.proposition, &example.target.proof),
        (
            Fact::ForallFact(_),
            LitexToLeanFactProofIr::ForallIntroduction { .. }
        )
    ) {
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            &example.block.well_definedness,
        )?;
        if !example.block.premise_aliases.is_empty()
            || !example.block.assumption_inferred_facts.is_empty()
        {
            return Err("forall example retained unsupported local assumption effects".into());
        }
        declarations.push(construct_lean_declaration_for_forall_fact(
            &example.target,
            &example.well_definedness,
            *fact_index,
            "example",
            &example.block.steps,
            context,
        )?);
        *fact_index += 1;
        return Ok(());
    }
    let mut nested = context.clone();
    let mut local_index = 0;
    let mut lines =
        render_local_proof_block(&example.block, &mut nested, "__step", &mut local_index)?;
    let proposition = render_fact(&example.target.proposition, &nested)?;
    lines.push(format!("exact {}", render_proof(&example.target, &nested)?));
    declarations.push(format!(
        "example : {proposition} := by\n{}",
        indent_lines(&lines.join("\n"), 2)
    ));
    *fact_index += 1;
    Ok(())
}

fn construct_lean_declaration_for_stored_fact(
    source: &LitexToLeanFactIr,
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    theorem_index: usize,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match (&source.proposition, &source.proof) {
        (Fact::ForallFact(_), LitexToLeanFactProofIr::ForallIntroduction { .. }) => {
            construct_lean_declaration_for_forall_fact(
                source,
                well_definedness,
                theorem_index,
                &format!("theorem __fact{theorem_index}"),
                &[],
                context,
            )
        }
        (Fact::ForallFact(forall), LitexToLeanFactProofIr::KnownFactCitation { .. }) => {
            Ok(format!(
                "theorem __fact{theorem_index} :\n    {} := {}",
                render_forall_fact_type(forall, context)?,
                render_proof(source, context)?
            ))
        }
        (Fact::AtomicFact(_), _)
        | (Fact::ExistFact(_), _)
        | (Fact::AndFact(_), _)
        | (Fact::OrFact(_), _)
        | (Fact::ChainFact(_), _) => construct_lean_declaration_for_direct_fact(
            source,
            well_definedness,
            theorem_index,
            context,
        ),
        other => Err(format!(
            "compiler currently cannot emit stored fact shape `{other:?}`"
        )),
    }
}

fn construct_lean_declaration_for_direct_fact(
    source: &LitexToLeanFactIr,
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    theorem_index: usize,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut local = context.clone();
    local.well_definedness = Some(well_definedness.clone());
    let proposition = render_fact(&source.proposition, &local)?;
    let mut proof_lines = if proof_requires_closed_numeric_well_definedness(&source.proof) {
        construct_lean_proof_lines_for_closed_numeric_well_definedness(
            well_definedness,
            theorem_index,
            &local,
        )?
    } else {
        Vec::new()
    };
    proof_lines.push(format!("  exact {}", render_proof(source, &local)?));
    Ok(format!(
        "theorem __fact{theorem_index} : {proposition} := by\n{}",
        proof_lines.join("\n")
    ))
}

fn construct_lean_proof_lines_for_closed_numeric_well_definedness(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
    theorem_index: usize,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Vec<String>, String> {
    if !certificate.target_requirements.is_empty()
        || !certificate.parameter_facts.is_empty()
        || !certificate.binder_scopes.is_empty()
    {
        return Err(
            "atomic equality has unsupported target, parameter, or binder WD evidence".into(),
        );
    }
    for root_use in &certificate.root_proof_uses {
        if !certificate
            .objects
            .iter()
            .any(|object| object.well_defined_obj_id == root_use.well_defined_obj_id)
        {
            return Err(format!(
                "WD proof use references unavailable object `{:?}`",
                root_use.well_defined_obj_id
            ));
        }
    }
    for source_use in &certificate.source_object_uses {
        let object = certificate
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == source_use.well_defined_obj_id)
            .ok_or_else(|| {
                format!(
                    "WD source use references unavailable object `{:?}`",
                    source_use.well_defined_obj_id
                )
            })?;
        if obj_equality_key(&source_use.source_object) != obj_equality_key(&object.source_object) {
            return Err("WD source use changed its retained object".into());
        }
    }
    for object in &certificate.objects {
        if !object.function_contracts.is_empty()
            || !object.ambient_binder_scope_ids.is_empty()
            || object.owned_binder_scope_id.is_some()
        {
            return Err(format!(
                "closed numeric WD object `{}` gained function or binder evidence",
                object.source_object
            ));
        }
        if object.intrinsic_result_set.as_ref().is_some_and(|set| {
            !matches!(
                set,
                LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Complex)
            )
        }) {
            return Err("closed numeric WD object has an unsupported intrinsic result set".into());
        }
        render_obj(&object.source_object, context)?;
        for child_use in &object.child_uses {
            let child = certificate
                .objects
                .iter()
                .find(|candidate| candidate.well_defined_obj_id == child_use.obj_id)
                .ok_or_else(|| {
                    format!(
                        "WD child references unavailable object `{:?}`",
                        child_use.obj_id
                    )
                })?;
            if obj_equality_key(&child.source_object) != obj_equality_key(&child_use.source_object)
            {
                return Err("WD child use changed its retained object".into());
            }
        }
        for fact_id in &object.well_defined_fact_ids {
            if !certificate
                .facts
                .iter()
                .any(|fact| fact.well_defined_fact_id == *fact_id)
            {
                return Err(format!(
                    "WD object references unavailable fact `{fact_id:?}`"
                ));
            }
        }
        for requirement in &object.target_requirements {
            let fact = certificate
                .facts
                .iter()
                .find(|fact| fact.well_defined_fact_id == requirement.well_defined_fact_id)
                .ok_or_else(|| {
                    format!(
                        "WD requirement references unavailable fact `{:?}`",
                        requirement.well_defined_fact_id
                    )
                })?;
            let _ = fact;
        }
    }

    let mut lines = Vec::new();
    for (index, fact) in certificate.facts.iter().enumerate() {
        if !fact.ambient_binder_scope_ids.is_empty() {
            return Err("closed numeric WD fact changed scope".into());
        }
        let proposition = render_fact(&fact.fact.proposition, context)?;
        let proof = render_proof(&fact.fact, context)?;
        lines.push(format!(
            "  have __wd{theorem_index}_{index} : {proposition} := {proof}"
        ));
    }
    Ok(lines)
}

fn construct_lean_declarations_for_named_set_aliases(
    source: &crate::litex_to_lean_ir::LitexToLeanHaveObjEqualStmtIr,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Vec<String>, String> {
    if source.definitions.is_empty() || source.facts.len() != source.definitions.len() * 2 {
        return Err("named set definition has unsupported certificate shape".into());
    }
    let mut declarations = Vec::new();
    for definition in &source.definitions {
        if definition.param_type != LitexToLeanParameterTypeIr::Set {
            return Err(format!(
                "compiler named object `{}` is not declared as a set",
                definition.name
            ));
        }
        let value = render_set_definition_value(&definition.value, context)?;
        let name = lean_identifier(&definition.name);
        if context
            .symbol_names
            .insert(definition.symbol_id, name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate compiler symbol identity for `{}`",
                definition.name
            ));
        }
        declarations.push(format!("abbrev {name} : Litex.Set := {value}"));
    }
    Ok(declarations)
}

fn construct_lean_declarations_for_compatibility_have_object_equal_result(
    source: &LitexToLeanHaveObjEqualStmtIr,
    declarations: &mut Vec<String>,
    fact_index: &mut usize,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &source.well_definedness,
    )?;
    if source
        .definitions
        .iter()
        .all(|definition| definition.param_type == LitexToLeanParameterTypeIr::Set)
    {
        declarations.extend(construct_lean_declarations_for_named_set_aliases(
            source, context,
        )?);
        return Ok(());
    }
    if source.definitions.len() != 1 || source.facts.len() != 2 {
        return Err(
            "compiler native object definition supports one membership-constrained object".into(),
        );
    }
    let definition = &source.definitions[0];
    if !matches!(
        definition.param_type,
        LitexToLeanParameterTypeIr::MemberOf { .. }
    ) {
        return Err(format!(
            "compiler native object `{}` requires an exact membership type",
            definition.name
        ));
    }
    let name = lean_identifier(&definition.name);
    let value = render_native_object_ir(&definition.value, context)?;
    if context
        .symbol_names
        .insert(definition.symbol_id, name.clone())
        .is_some()
    {
        return Err(format!(
            "duplicate compiler symbol identity for `{}`",
            definition.name
        ));
    }
    declarations.push(format!("noncomputable def {name} := {value}"));
    construct_lean_declarations_for_stored_fact_effects(
        source.facts.iter().collect(),
        &source.well_definedness,
        declarations,
        fact_index,
        context,
    )
}

fn render_set_definition_value(
    value: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match value {
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) => Ok("Litex.R".into()),
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Complex) => Ok("Litex.C".into()),
        LitexToLeanObjectIr::SetBuilder(_) => render_set_ir(value, context),
        _ => Err(format!(
            "unsupported compiler named set definition value `{value:?}`"
        )),
    }
}

fn construct_lean_declaration_for_forall_fact(
    source: &LitexToLeanFactIr,
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    theorem_index: usize,
    declaration: &str,
    proof_steps: &[LitexToLeanStatementIr],
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::ForallFact(forall) = &source.proposition else {
        return Err("compiler currently emits `forall` facts only".into());
    };
    let LitexToLeanFactProofIr::ForallIntroduction {
        parameter_premises,
        premises,
        inferred_premises,
        conclusions,
    } = &source.proof
    else {
        return Err("verified forall is missing ForallIntroduction evidence".into());
    };
    let params = forall
        .params_def_with_type
        .collect_param_bindings_with_types();
    if params.len() != parameter_premises.len() {
        return Err("forall parameter evidence count does not match source binders".into());
    }
    if forall.dom_facts.len() != premises.len() {
        return Err("forall domain evidence count does not match source premises".into());
    }
    if forall.then_facts.len() != conclusions.len() {
        return Err("forall conclusion evidence count does not match source conclusions".into());
    }

    let mut context = outer_context.clone();
    context.well_definedness = Some(well_definedness.clone());
    let mut binders = Vec::new();
    let mut intro_names = Vec::new();
    for (parameter_index, ((binding, param_type), premise)) in
        params.iter().zip(parameter_premises.iter()).enumerate()
    {
        let name = lean_identifier(binding.name());
        context.symbol_names.insert(binding.id(), name.clone());
        if matches!(param_type, ParamType::Set(_)) {
            validate_set_parameter_premise(binding.id(), &premise.fact)?;
            binders.push(format!("({name} : Litex.Set)"));
            intro_names.push(name);
            continue;
        }
        if matches!(
            param_type,
            ParamType::NonemptySet(_) | ParamType::FiniteSet(_)
        ) {
            validate_refined_set_parameter_premise(binding.id(), param_type, &premise.fact)?;
            binders.push(format!("({name} : Litex.Set)"));
            intro_names.push(name.clone());
            let actual = render_fact(&premise.fact, &context)?;
            let hypothesis = format!("__h{theorem_index}_{}", parameter_index + 1);
            binders.push(format!("({hypothesis} : {actual})"));
            intro_names.push(hypothesis.clone());
            context.fact_names.insert(premise.fact_id, hypothesis);
            context
                .fact_propositions
                .insert(premise.fact_id, premise.fact.clone());
            continue;
        }

        let set = parameter_set(param_type)?;
        let carrier_name = format!("__carrier{theorem_index}_{}", parameter_index + 1);
        match set {
            Obj::FnSet(_) => {
                binders.push(format!("{{{carrier_name} : Type 1}}"));
                intro_names.push(carrier_name.clone());
                binders.push(format!("({name} : {carrier_name})"));
            }
            set if set_requires_heterogeneous_carrier(set) => {
                binders.push(format!("{{{carrier_name} : Type}}"));
                intro_names.push(carrier_name.clone());
                binders.push(format!("({name} : {carrier_name})"));
            }
            _ => binders.push(format!("({name} : ℂ)")),
        }
        intro_names.push(name.clone());

        let expected = format!("Litex.In {name} {}", render_obj(set, &context)?);
        let actual = render_fact(&premise.fact, &context)?;
        if actual != expected {
            return Err(format!(
                "parameter evidence mismatch: expected `{expected}`, found `{actual}`"
            ));
        }
        let hypothesis = format!("__h{theorem_index}_{}", parameter_index + 1);
        binders.push(format!("({hypothesis} : {actual})"));
        intro_names.push(hypothesis.clone());
        context.fact_names.insert(premise.fact_id, hypothesis);
        context
            .fact_propositions
            .insert(premise.fact_id, premise.fact.clone());
        if let Obj::FnSet(function_set) = set {
            let function = LitexToLeanFunctionTypeIr::lower(function_set)?;
            validate_function_type(&function)?;
            context.function_bindings.insert(
                premise.fact_id,
                FunctionBinding {
                    symbol_id: binding.id(),
                    function,
                    membership_proof_name: format!("__h{theorem_index}_{}", parameter_index + 1),
                    direct: false,
                },
            );
        }
        install_parameter_fact_aliases(
            binding.id(),
            &premise.fact,
            &format!("__h{theorem_index}_{}", parameter_index + 1),
            set,
            &mut context,
        )?;
    }

    for (premise_index, premise) in premises.iter().enumerate() {
        let actual = render_fact(&premise.fact, &context)?;
        let hypothesis = format!(
            "__h{theorem_index}_{}",
            parameter_premises.len() + premise_index + 1
        );
        binders.push(format!("({hypothesis} : {actual})"));
        intro_names.push(hypothesis.clone());
        context.fact_names.insert(premise.fact_id, hypothesis);
        context
            .fact_propositions
            .insert(premise.fact_id, premise.fact.clone());
    }

    // Inferred premises are verifier-owned consequences of the explicit
    // binders above. Materialize only inference routes with reviewed proof
    // adapters so later exact FactId citations can resolve them.
    let mut derived_lines = Vec::new();
    for (inferred_index, inferred) in inferred_premises.iter().enumerate() {
        let proposition = render_fact(&inferred.proposition, &context)?;
        let supported = matches!(
            &inferred.proof,
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ConjunctionProjection { .. }
                    | LitexToLeanProofRuleIr::Builtin(
                        LitexToLeanBuiltinRuleIr::PositiveRealMembership
                            | LitexToLeanBuiltinRuleIr::NonzeroNumericMembershipElimination
                    ),
                ..
            }
        );
        if !supported {
            continue;
        }
        let proof = render_proof(inferred, &context)?;
        let name = format!("__i{theorem_index}_{inferred_index}");
        derived_lines.push(format!("  have {name} : {proposition} := {proof}"));
        if let Some(fact_id) = inferred.stored_fact_id() {
            context.fact_names.insert(fact_id, name);
            context
                .fact_propositions
                .insert(fact_id, inferred.proposition.clone());
        }
    }

    let conclusion_types = conclusions
        .iter()
        .map(|conclusion| render_fact(&conclusion.proposition, &context))
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion_type = conjunction(&conclusion_types);
    let mut local_index = 0;
    for local in render_local_statements(proof_steps, &mut context, "__step", &mut local_index)? {
        derived_lines.push(indent_lines(&local, 2));
    }
    let single_heterogeneous_subset = conclusions.len() == 1
        && matches!(
            &conclusions[0].proposition,
            Fact::AtomicFact(AtomicFact::SubsetFact(_) | AtomicFact::SupersetFact(_))
        );
    if single_heterogeneous_subset {
        // Keep the proof expression under the theorem conclusion's expected
        // type. In particular, `Litex.Subset` is a heterogeneous dependent
        // function; first assigning its proof to a standalone local can
        // prematurely instantiate its implicit carrier metavariable.
        derived_lines.push(format!(
            "  exact {}",
            render_proof(&conclusions[0], &context)?
        ));
    } else {
        let mut conclusion_names = Vec::with_capacity(conclusions.len());
        for (conclusion_index, conclusion) in conclusions.iter().enumerate() {
            let proposition = &conclusion_types[conclusion_index];
            let proof = render_proof(conclusion, &context)?;
            let name = format!("__c{theorem_index}_{conclusion_index}");
            derived_lines.push(format!("  have {name} : {proposition} := {proof}"));
            if let Some(fact_id) = conclusion.stored_fact_id() {
                context.fact_names.insert(fact_id, name.clone());
                context
                    .fact_propositions
                    .insert(fact_id, conclusion.proposition.clone());
            }
            conclusion_names.push(name);
        }
        if conclusion_names.len() == 1 {
            derived_lines.push(format!("  exact {}", conclusion_names[0]));
        } else {
            derived_lines.push(format!("  exact ⟨{}⟩", conclusion_names.join(", ")));
        }
    }
    let theorem_type = if binders.is_empty() {
        conclusion_type
    } else {
        format!("∀ {},\n      {conclusion_type}", binders.join(" "))
    };
    let intro = if intro_names.is_empty() {
        String::new()
    } else {
        format!("  intro {}\n", intro_names.join(" "))
    };
    Ok(format!(
        "{declaration} :\n    {theorem_type} := by\n{intro}{}",
        derived_lines.join("\n")
    ))
}

fn render_forall_fact_type(
    forall: &ForallFact,
    outer_context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut context = outer_context.clone();
    let mut binders = Vec::new();
    for (index, (binding, param_type)) in forall
        .params_def_with_type
        .collect_param_bindings_with_types()
        .iter()
        .enumerate()
    {
        let name = format!("__p{}", index + 1);
        context.symbol_names.insert(binding.id(), name.clone());
        if matches!(param_type, ParamType::Set(_)) {
            binders.push(format!("({name} : Litex.Set)"));
            continue;
        }
        if matches!(
            param_type,
            ParamType::NonemptySet(_) | ParamType::FiniteSet(_)
        ) {
            binders.push(format!("({name} : Litex.Set)"));
            let property = match param_type {
                ParamType::NonemptySet(_) => "Litex.Set.Nonempty",
                ParamType::FiniteSet(_) => "Litex.Set.Finite",
                _ => unreachable!("refined-set branch checked above"),
            };
            binders.push(format!("(__type{} : {property} {name})", index + 1));
            let expected = match param_type {
                ParamType::NonemptySet(_) => {
                    format!("Litex.Set.Nonempty {name}")
                }
                ParamType::FiniteSet(_) => format!("Litex.Set.Finite {name}"),
                _ => unreachable!("refined-set branch checked above"),
            };
            install_rendered_parameter_aliases(
                binding.id(),
                &expected,
                &format!("__type{}", index + 1),
                None,
                &mut context,
            )?;
            continue;
        }

        let set = parameter_set(param_type)?;
        let carrier = format!("__carrier{}", index + 1);
        match set {
            Obj::FnSet(_) => {
                binders.push(format!("{{{carrier} : Type 1}}"));
                binders.push(format!("({name} : {carrier})"));
            }
            set if set_requires_heterogeneous_carrier(set) => {
                binders.push(format!("{{{carrier} : Type}}"));
                binders.push(format!("({name} : {carrier})"));
            }
            _ => binders.push(format!("({name} : ℂ)")),
        }
        binders.push(format!(
            "(__type{} : Litex.In {name} {})",
            index + 1,
            render_obj(set, &context)?
        ));
        let expected = format!("Litex.In {name} {}", render_obj(set, &context)?);
        install_rendered_parameter_aliases(
            binding.id(),
            &expected,
            &format!("__type{}", index + 1),
            match set {
                Obj::FnSet(function) => Some(LitexToLeanFunctionTypeIr::lower(function)?),
                _ => None,
            },
            &mut context,
        )?;
    }
    for (index, premise) in forall.dom_facts.iter().enumerate() {
        binders.push(format!(
            "(__domain{} : {})",
            index + 1,
            render_fact(premise, &context)?
        ));
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|conclusion| render_fact(&conclusion.clone().to_fact(), &context))
        .collect::<Result<Vec<_>, _>>()?;
    if conclusions.is_empty() {
        return Err("forall citation retained no conclusions".into());
    }
    Ok(format!(
        "∀ {}, {}",
        binders.join(" "),
        conjunction(&conclusions)
    ))
}

fn install_parameter_fact_aliases(
    symbol_id: SymbolId,
    proposition: &Fact,
    proof_name: &str,
    set: &Obj,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let function = match set {
        Obj::FnSet(function) => Some(LitexToLeanFunctionTypeIr::lower(function)?),
        _ => None,
    };
    let expected = render_fact(proposition, context)?;
    install_rendered_parameter_aliases(symbol_id, &expected, proof_name, function, context)
}

fn install_rendered_parameter_aliases(
    symbol_id: SymbolId,
    expected: &str,
    proof_name: &str,
    function: Option<LitexToLeanFunctionTypeIr>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let aliases = context
        .well_definedness
        .as_ref()
        .map(|certificate| certificate.parameter_facts.clone())
        .unwrap_or_default();
    for alias in aliases {
        if alias.symbol_id != symbol_id || render_fact(&alias.proposition, context)? != expected {
            continue;
        }
        context
            .fact_names
            .insert(alias.fact_id, proof_name.to_string());
        context
            .fact_propositions
            .insert(alias.fact_id, alias.proposition.clone());
        if let Some(function) = &function {
            context.function_bindings.insert(
                alias.fact_id,
                FunctionBinding {
                    symbol_id,
                    function: function.clone(),
                    membership_proof_name: proof_name.to_string(),
                    direct: false,
                },
            );
        }
    }
    Ok(())
}

fn render_local_proof_block(
    block: &LitexToLeanLocalProofBlockIr,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
    prefix: &str,
    local_index: &mut usize,
) -> Result<Vec<String>, String> {
    crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
        &block.well_definedness,
    )?;
    for alias in &block.premise_aliases {
        let proposition = context
            .fact_propositions
            .get(&alias.parent_fact_id)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "local alias references unavailable parent FactId `{}`",
                    alias.parent_fact_id
                )
            })?;
        let parent_name = resolve_fact_citation(&alias.parent_fact_id, &proposition, context)?;
        context.fact_names.insert(alias.local_fact_id, parent_name);
        context
            .fact_propositions
            .insert(alias.local_fact_id, proposition);
    }
    let mut lines = Vec::new();
    for inferred in &block.assumption_inferred_facts {
        lines.push(render_local_fact(
            inferred,
            &block.well_definedness,
            context,
            prefix,
            local_index,
        )?);
    }
    lines.extend(render_local_statements(
        &block.steps,
        context,
        prefix,
        local_index,
    )?);
    Ok(lines)
}

fn render_local_statements(
    statements: &[LitexToLeanStatementIr],
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
    prefix: &str,
    local_index: &mut usize,
) -> Result<Vec<String>, String> {
    let mut lines = Vec::new();
    for statement in statements {
        if let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::LetObjStmt(definition)) =
            statement
        {
            crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                &definition.well_definedness,
            )?;
            let name = lean_identifier(&definition.name);
            let value = render_native_object_ir(&definition.value, context)?;
            if context
                .symbol_names
                .insert(definition.symbol_id, name.clone())
                .is_some()
            {
                return Err(format!(
                    "duplicate local compiler symbol identity for `{}`",
                    definition.name
                ));
            }
            lines.push(format!("let {name} := {value}"));
            for fact in std::iter::once(&definition.defining_equality)
                .chain(definition.inferred_facts.iter())
            {
                lines.push(render_local_fact(
                    fact,
                    &definition.well_definedness,
                    context,
                    prefix,
                    local_index,
                )?);
            }
            continue;
        }
        let (facts, well_definedness) = match statement {
            LitexToLeanStatementIr::Fact(statement) => {
                if !statement.stored_projections.is_empty() {
                    return Err(
                        "compiler local proof does not yet emit stored forall projections".into(),
                    );
                }
                (
                    std::iter::once(&statement.source)
                        .chain(statement.inferred_facts.iter())
                        .collect::<Vec<_>>(),
                    &statement.well_definedness,
                )
            }
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(statement)) => (
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
            ),
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(statement)) => (
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
            ),
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(statement)) => (
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
            ),
            LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(
                statement,
            )) => (
                statement
                    .facts
                    .iter()
                    .chain(statement.inferred_facts.iter())
                    .collect::<Vec<_>>(),
                &statement.well_definedness,
            ),
            other => {
                return Err(format!(
                    "unsupported local proof statement in compiler MVP: {other:?}"
                ));
            }
        };
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            well_definedness,
        )?;
        for fact in facts {
            lines.push(render_local_fact(
                fact,
                well_definedness,
                context,
                prefix,
                local_index,
            )?);
        }
    }
    Ok(lines)
}

fn render_local_fact(
    fact: &LitexToLeanFactIr,
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
    prefix: &str,
    local_index: &mut usize,
) -> Result<String, String> {
    *local_index += 1;
    let name = format!("{prefix}{local_index}");
    let proposition = render_fact(&fact.proposition, context)?;
    let mut proof_lines = if proof_requires_closed_numeric_well_definedness(&fact.proof) {
        construct_lean_proof_lines_for_closed_numeric_well_definedness(
            well_definedness,
            *local_index,
            context,
        )?
    } else {
        Vec::new()
    };
    proof_lines.push(format!("  exact {}", render_proof(fact, context)?));
    if let Some(fact_id) = fact.stored_fact_id() {
        context.fact_names.insert(fact_id, name.clone());
        context
            .fact_propositions
            .insert(fact_id, fact.proposition.clone());
    }
    Ok(format!(
        "have {name} : {proposition} := by\n{}",
        proof_lines.join("\n")
    ))
}

fn render_proof(
    fact: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match &fact.proof {
        LitexToLeanFactProofIr::UseBuiltinStrategy { proof } => {
            let unwrapped = LitexToLeanFactIr {
                storage: fact.storage,
                proposition: fact.proposition.clone(),
                proof: proof.as_ref().clone(),
            };
            render_proof(&unwrapped, context)
        }
        LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
            resolve_fact_citation(source_fact_id, &fact.proposition, context)
        }
        LitexToLeanFactProofIr::ExistentialAlphaRenameCitation { source_fact_id } => {
            let stored = context
                .fact_propositions
                .get(source_fact_id)
                .ok_or_else(|| {
                    format!("existential citation references unavailable FactId `{source_fact_id}`")
                })?;
            if !one_witness_existentials_are_alpha_equal(stored, &fact.proposition, context)? {
                return Err(
                    "existential citation changed its retained source or alpha-equivalent target"
                        .into(),
                );
            }
            context
                .fact_names
                .get(source_fact_id)
                .cloned()
                .ok_or_else(|| {
                    format!("existential citation FactId `{source_fact_id}` has no Lean name")
                })
        }
        LitexToLeanFactProofIr::ObjectDefinitionEquality => {
            render_object_definition_equality(fact, context)
        }
        LitexToLeanFactProofIr::ObjectDefinitionMembership { value_check } => {
            render_object_definition_membership(fact, value_check, context)
        }
        LitexToLeanFactProofIr::ObjectChoice => render_object_choice(fact, context),
        LitexToLeanFactProofIr::CaseSplit { coverage, branches } => {
            render_case_split(fact, coverage, branches, context)
        }
        LitexToLeanFactProofIr::ByContradiction {
            reverse_assumption,
            block,
            contradiction,
        } => render_by_contradiction(fact, reverse_assumption, block, contradiction, context),
        LitexToLeanFactProofIr::RuleApplication {
            rule,
            parameter_requirements,
            premises,
        } => match rule {
            LitexToLeanProofRuleIr::ObjectReflexivity
                if parameter_requirements.is_empty() && premises.is_empty() =>
            {
                let (left, right) = equality_parts(&fact.proposition)?;
                if obj_equality_key(left) != obj_equality_key(right) {
                    return Err("object-reflexivity certificate changed its equality".into());
                }
                Ok(format!("Litex.Same.refl {}", render_obj(left, context)?))
            }
            LitexToLeanProofRuleIr::RationalNormalization
                if parameter_requirements.is_empty() && premises.is_empty() =>
            {
                let (left, right) = equality_parts(&fact.proposition)?;
                if !objs_equal_by_rational_expression_evaluation(left, right) {
                    return Err(
                        "rational-normalization certificate does not match its equality".into(),
                    );
                }
                render_obj(left, context)?;
                render_obj(right, context)?;
                Ok(
                    "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                        .into(),
                )
            }
            LitexToLeanProofRuleIr::RationalNormalization
                if parameter_requirements.is_empty() && premises.len() == 1 =>
            {
                let (target_left, target_right) = equality_parts(&fact.proposition)?;
                let (source_left, source_right) = equality_parts(&premises[0].proposition)?;
                if !objects_match_after_rational_normalization(target_left, source_left)
                    || !objects_match_after_rational_normalization(target_right, source_right)
                {
                    return Err(
                        "premise-backed rational normalization changed its equality endpoints"
                            .into(),
                    );
                }
                let source_proof = render_proof(&premises[0], context)?;
                render_fact(&fact.proposition, context)?;
                Ok(format!(
                    "(by\n  convert {source_proof} using 1 <;> norm_num)"
                ))
            }
            LitexToLeanProofRuleIr::ClosedStandardMembership
                if parameter_requirements.is_empty() && premises.is_empty() =>
            {
                render_closed_standard_membership(fact, context)
            }
            LitexToLeanProofRuleIr::ClosedNumericMembership(evidence)
                if parameter_requirements.is_empty() && premises.is_empty() =>
            {
                render_closed_numeric_membership(fact, evidence, context)
            }
            LitexToLeanProofRuleIr::StandardSetNonempty
                if parameter_requirements.is_empty() && premises.is_empty() =>
            {
                render_standard_set_nonempty(fact, context)
            }
            LitexToLeanProofRuleIr::ClosedNumericComparison => {
                render_closed_numeric_comparison(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::NotEqualSymmetry) => {
                render_not_equal_symmetry(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection,
            ) => render_standard_set_membership_projection(
                fact,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::StandardSetSubset) => {
                render_standard_set_subset(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Set(rule)) => {
                render_set_builtin_rule(fact, *rule, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::FiniteSet(rule)) => {
                render_finite_set_constructor(
                    fact,
                    *rule,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::ListSetMembership {
                selected_index,
            }) => render_list_set_membership(
                fact,
                *selected_index,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::ListSetMembershipElimination,
            ) => render_list_set_membership_elimination(
                fact,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::TupleLiteralShape) => {
                render_tuple_literal_shape(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(
                rule @ (LitexToLeanBuiltinRuleIr::PrimeU64Reflection
                | LitexToLeanBuiltinRuleIr::CoprimeNaturalReflection),
            ) => render_number_theory_reflection(
                fact,
                rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::NonzeroNumericMembership) => {
                render_nonzero_numeric_membership(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::NonzeroNumericMembershipElimination,
            ) => render_nonzero_numeric_membership_elimination(
                fact,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::NativeConstantMembership(rule),
            ) => render_native_constant_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
            ),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::PositiveRealMembership) => {
                render_positive_real_membership(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::NaturalMembershipImpliesNonnegative,
            ) => render_natural_membership_implies_nonnegative(
                fact,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::ComplexArithmeticMembershipClosure(rule),
            ) => render_complex_binary_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::IntegerMembershipClosure(rule),
            ) => render_integer_binary_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::NaturalMembershipClosure(rule),
            ) => render_natural_binary_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::RationalMembershipClosure(rule),
            ) => render_rational_binary_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(
                LitexToLeanBuiltinRuleIr::RealArithmeticMembershipClosure(
                    rule @ (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add
                    | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub
                    | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul
                    | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div),
                ),
            ) => render_real_binary_membership_rule(
                fact,
                *rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Arithmetic(
                LitexToLeanArithmeticBuiltinRuleIr::OrderTransitivity,
            )) => render_order_transitivity(fact, parameter_requirements, premises, context),
            LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Arithmetic(
                rule @ (LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative
                | LitexToLeanArithmeticBuiltinRuleIr::AddPositive
                | LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict
                | LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict
                | LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative
                | LitexToLeanArithmeticBuiltinRuleIr::MulPositive
                | LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative
                | LitexToLeanArithmeticBuiltinRuleIr::DivPositive),
            )) => render_additive_sign_rule(fact, *rule, parameter_requirements, premises, context),
            LitexToLeanProofRuleIr::ComparisonNotationDuality => {
                render_comparison_notation_duality(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::EqualityRewrite => {
                construct_lean_proof_for_membership_equality_rewrite(
                    fact,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::KnownEqualityPath => {
                render_known_equality_path(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::KnownForallInstantiation {
                source_fact_id,
                arguments,
            } => render_known_forall_instantiation(
                fact,
                *source_fact_id,
                arguments,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::AndIntroduction => {
                render_and_introduction(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::DisjunctionIntroduction { selected_index } => {
                render_disjunction_introduction(
                    fact,
                    *selected_index,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::ConjunctionProjection { index } => {
                render_conjunction_projection(
                    fact,
                    *index,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::DefinitionReduction => {
                render_definition_reduction(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::DefinitionProjection => {
                render_definition_projection(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::DefinitionIntroduction => {
                render_definition_introduction(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::CheckedFunctionDefinitionReduction {
                defining_equality_fact_id,
                application_side,
            } => render_checked_identity_function_reduction(
                fact,
                *defining_equality_fact_id,
                *application_side,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanProofRuleIr::SetBuilderMembership => {
                render_set_builder_membership(fact, parameter_requirements, premises, context)
            }
            LitexToLeanProofRuleIr::SetBuilderBaseMembershipProjection => {
                render_set_builder_base_membership_projection(
                    fact,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::SetBuilderPredicateProjection { clause_index } => {
                render_set_builder_predicate_projection(
                    fact,
                    *clause_index,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::ExistIntroduction { witnesses, steps } => {
                render_exist_introduction(
                    fact,
                    witnesses,
                    steps,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            LitexToLeanProofRuleIr::RegisteredRule(rule) => {
                construct_lean_proof_for_registered_rule(
                    fact,
                    rule,
                    parameter_requirements,
                    premises,
                    context,
                )
            }
            other => Err(format!("unsupported verified proof rule: {other:?}")),
        },
        other => Err(format!("unsupported verified proof evidence: {other:?}")),
    }
}

fn objects_match_after_rational_normalization(left: &Obj, right: &Obj) -> bool {
    if objs_equal_by_rational_expression_evaluation(left, right) {
        return true;
    }
    let (Obj::FnObj(left), Obj::FnObj(right)) = (left, right) else {
        return false;
    };
    left.head.to_string() == right.head.to_string()
        && left.body.len() == right.body.len()
        && left
            .body
            .iter()
            .zip(right.body.iter())
            .all(|(left, right)| {
                left.len() == right.len()
                    && left.iter().zip(right.iter()).all(|(left, right)| {
                        objects_match_after_rational_normalization(left, right)
                    })
            })
}

fn proof_requires_closed_numeric_well_definedness(proof: &LitexToLeanFactProofIr) -> bool {
    match proof {
        LitexToLeanFactProofIr::UseBuiltinStrategy { proof } => {
            proof_requires_closed_numeric_well_definedness(proof)
        }
        LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::RationalNormalization,
            ..
        } => true,
        _ => false,
    }
}

fn render_object_definition_membership(
    target: &LitexToLeanFactIr,
    value_check: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (target_element, target_set) = membership_parts(&target.proposition)?;
    let (source_element, source_set) = membership_parts(&value_check.proposition)?;
    if !matches!(
        LitexToLeanObjectIr::lower(target_element)?,
        LitexToLeanObjectIr::Symbol { .. }
    ) {
        return Err("object-definition membership target is not the declared symbol".into());
    }
    let name = render_obj(target_element, context)?;
    if obj_equality_key(target_set) != obj_equality_key(source_set) {
        return Err("object definition changed its retained membership check".into());
    }
    render_obj(source_element, context)?;
    Ok(format!(
        "(by\n  unfold {name}\n  exact {})",
        render_proof(value_check, context)?
    ))
}

fn render_object_definition_equality(
    target: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(&target.proposition)?;
    if !matches!(
        LitexToLeanObjectIr::lower(left)?,
        LitexToLeanObjectIr::Symbol { .. }
    ) {
        return Err("object-definition equality target is not the declared symbol".into());
    }
    let name = render_obj(left, context)?;
    let rendered_value = render_obj(right, context)?;
    Ok(format!(
        "(by\n  unfold {name}\n  exact Litex.Same.refl {rendered_value})"
    ))
}

fn render_object_choice(
    target: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, target_set) = membership_parts(&target.proposition)?;
    if !matches!(
        LitexToLeanObjectIr::lower(element)?,
        LitexToLeanObjectIr::Symbol { .. }
    ) {
        return Err("object-choice membership target is not the chosen symbol".into());
    }
    let name = render_obj(element, context)?;
    let carrier = LitexToLeanObjectIr::lower(target_set)?;
    Ok(format!(
        "Litex.In.own {} {name}",
        render_set_ir(&carrier, context)?
    ))
}

fn render_standard_set_nonempty(
    target: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) = &target.proposition else {
        return Err("standard-set nonemptiness proof targets another proposition".into());
    };
    let theorem = match &fact.set {
        Obj::StandardSet(StandardSet::N) => "Litex.Rules.naturalNonempty",
        Obj::StandardSet(StandardSet::Z) => "Litex.Rules.integerNonempty",
        Obj::StandardSet(StandardSet::Q) => "Litex.Rules.rationalNonempty",
        Obj::StandardSet(StandardSet::R) => "Litex.Rules.realNonempty",
        Obj::StandardSet(StandardSet::C) => "Litex.Rules.complexNonempty",
        _ => {
            return Err(format!("unsupported nonempty-set carrier `{}`", fact.set));
        }
    };
    let expected = format!("Litex.Set.Nonempty {}", render_obj(&fact.set, context)?);
    if render_fact(&target.proposition, context)? != expected {
        return Err("standard-set nonemptiness changed its rendered target".into());
    }
    Ok(theorem.into())
}

fn render_definition_reduction(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = &target.proposition else {
        return Err("concrete predicate reduction targets a non-predicate fact".into());
    };
    let definition = predicate.predicate.to_string();
    let binding = context
        .predicate_bindings
        .get(&definition)
        .ok_or_else(|| format!("unavailable concrete predicate definition `{definition}`"))?;
    if predicate.body.len() != binding.parameter_count
        || parameter_requirements.len() != binding.requirement_count
        || premises.len() != binding.clause_count
    {
        return Err("concrete predicate reduction changed its definition contract".into());
    }
    let expected_components =
        instantiated_predicate_components(&target.proposition, binding, context)?;
    for (actual, expected) in parameter_requirements
        .iter()
        .chain(premises.iter())
        .zip(expected_components.iter())
    {
        if render_fact(&actual.proposition, context)? != *expected {
            return Err("concrete predicate reduction changed a parameter requirement".into());
        }
    }
    let proofs = parameter_requirements
        .iter()
        .chain(premises.iter())
        .map(|proof| render_proof(proof, context))
        .collect::<Result<Vec<_>, _>>()?;
    if proofs.is_empty() {
        return Err("concrete predicate reduction retained no proof components".into());
    }
    Ok(format!(
        "(by\n  unfold {}\n  exact ⟨{}⟩)",
        binding.lean_name,
        proofs.join(", ")
    ))
}

fn render_definition_projection(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err("concrete predicate projection changed its source or target".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)) = &premises[0].proposition else {
        return Err("concrete predicate projection source is not a predicate fact".into());
    };
    let definition = source.predicate.to_string();
    let binding = context
        .predicate_bindings
        .get(&definition)
        .ok_or_else(|| format!("unavailable concrete predicate definition `{definition}`"))?;
    let components = instantiated_predicate_components(&premises[0].proposition, binding, context)?;
    let rendered_target = render_fact(&target.proposition, context)?;
    let indices = components
        .iter()
        .enumerate()
        .filter_map(|(index, component)| (component == &rendered_target).then_some(index))
        .collect::<Vec<_>>();
    let Some(index) = indices.first() else {
        return Err("concrete predicate projection target is not a definition component".into());
    };
    let selector = conjunction_selector(*index, components.len())?;
    Ok(format!(
        "(by\n  have __definition := {}\n  unfold {} at __definition\n  exact __definition{selector})",
        render_proof(&premises[0], context)?,
        binding.lean_name
    ))
}

fn render_definition_introduction(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err("concrete predicate introduction changed its source or target".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = &target.proposition else {
        return Err("concrete predicate introduction target is not a predicate fact".into());
    };
    let definition = predicate.predicate.to_string();
    let binding = context
        .predicate_bindings
        .get(&definition)
        .ok_or_else(|| format!("unavailable concrete predicate definition `{definition}`"))?;
    let components = instantiated_predicate_components(&target.proposition, binding, context)?;
    if components.len() != 1 || components[0] != render_fact(&premises[0].proposition, context)? {
        return Err(
            "concrete predicate introduction currently requires one exact definition component"
                .into(),
        );
    }
    Ok(format!(
        "(by\n  unfold {}\n  exact {})",
        binding.lean_name,
        render_proof(&premises[0], context)?
    ))
}

fn render_checked_identity_function_reduction(
    target: &LitexToLeanFactIr,
    defining_equality_fact_id: crate::common::fact_id::FactId,
    application_side: LitexToLeanEqualitySideIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("checked function reduction changed its verifier certificate".into());
    }
    let binding = context
        .named_function_definitions
        .get(&defining_equality_fact_id)
        .ok_or_else(|| {
            format!(
                "checked function reduction references unavailable defining FactId `{defining_equality_fact_id}`"
            )
        })?;
    let (target_left, target_right) = equality_parts(&target.proposition)?;
    let application_object = match application_side {
        LitexToLeanEqualitySideIr::Left => target_left,
        LitexToLeanEqualitySideIr::Right => target_right,
    };
    let LitexToLeanObjectIr::FunctionApplication(application) =
        LitexToLeanObjectIr::lower(application_object)?
    else {
        return Err("checked function reduction retained a non-application side".into());
    };
    if application.argument_layers.len() != 1
        || application.source_argument_layers.len() != 1
        || application.argument_layers[0].len() != binding.function.parameters.len()
        || application.source_argument_layers[0].len() != binding.function.parameters.len()
    {
        return Err("checked function reduction changed its one-layer parameter telescope".into());
    }
    let LitexToLeanObjectIr::Symbol {
        symbol_id: head_symbol_id,
        ..
    } = application.head.as_ref()
    else {
        return Err("checked function reduction requires a named head".into());
    };
    if *head_symbol_id != binding.symbol_id {
        return Err("checked function reduction changed its checked substitution".into());
    }

    let certificate = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "checked function reduction has no active WD certificate".to_string())?;
    let requirements = certificate
        .target_requirements
        .iter()
        .filter(|requirement| requirement.source_occurrence_id == application.source_occurrence_id)
        .collect::<Vec<_>>();
    if requirements.len() != binding.function.parameters.len() + binding.function.domain_facts.len()
    {
        return Err(
            "checked function reduction changed its exact application requirement count".into(),
        );
    }
    let mut definition_context = context.clone();
    definition_context.well_definedness = Some(binding.well_definedness.clone());
    let mut argument_evidence = HashMap::new();
    for (parameter_index, ((parameter, source_argument), local_premise)) in binding
        .function
        .parameters
        .iter()
        .zip(application.source_argument_layers[0].iter())
        .zip(binding.parameter_premises.iter())
        .enumerate()
    {
        let matches = requirements
            .iter()
            .filter(|requirement| {
                requirement.role
                    == (WellDefinednessRequirementRole::FunctionArgumentMembership {
                        layer_index: 0,
                        parameter_index,
                    })
            })
            .collect::<Vec<_>>();
        let [argument_requirement] = matches.as_slice() else {
            return Err(format!(
                "checked function reduction requires one argument-membership WD edge for parameter {parameter_index}"
            ));
        };
        let argument_fact = certificate
            .facts
            .iter()
            .find(|fact| fact.well_defined_fact_id == argument_requirement.well_defined_fact_id)
            .ok_or_else(|| {
                format!(
                    "checked function reduction lost argument-membership proof {parameter_index}"
                )
            })?;
        let argument = render_obj(source_argument, context)?;
        let argument_membership = render_proof(&argument_fact.fact, context)?;
        let expected_membership = format!(
            "Litex.In {argument} {}",
            render_set_ir(&parameter.set, &definition_context)?
        );
        let retained_membership = render_fact(&argument_fact.fact.proposition, context)?;
        if retained_membership != expected_membership {
            return Err(format!(
                "checked function reduction parameter {parameter_index} expected `{expected_membership}`, retained `{retained_membership}`"
            ));
        }
        definition_context
            .symbol_names
            .insert(parameter.symbol_id, argument.clone());
        definition_context
            .fact_names
            .insert(local_premise.fact_id, argument_membership.clone());
        definition_context
            .fact_propositions
            .insert(local_premise.fact_id, local_premise.fact.clone());
        if let Some(real) = membership_real_value(&parameter.set, &argument, &argument_membership) {
            definition_context
                .numeric_real_values
                .insert(parameter.symbol_id, real);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) =
            membership_numeric_proof(&parameter.set, &argument, &argument_membership)
        {
            definition_context
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
        argument_evidence.insert(
            parameter.symbol_id,
            (argument, argument_membership, parameter.set.clone()),
        );
    }
    let mut source_domain_definition_context = definition_context.clone();
    for (symbol_id, (source_argument, _, _)) in &argument_evidence {
        source_domain_definition_context
            .numeric_representations
            .insert(*symbol_id, source_argument.clone());
    }
    for (domain_index, (source_fact, local_premise)) in binding
        .function
        .domain_facts
        .iter()
        .zip(binding.domain_premises.iter())
        .enumerate()
    {
        let matches = requirements
            .iter()
            .filter(|requirement| {
                requirement.role
                    == (WellDefinednessRequirementRole::FunctionDomain {
                        layer_index: 0,
                        domain_index,
                    })
            })
            .collect::<Vec<_>>();
        let [domain_requirement] = matches.as_slice() else {
            return Err(format!(
                "checked function reduction requires one domain WD edge for clause {domain_index}"
            ));
        };
        let domain_fact = certificate
            .facts
            .iter()
            .find(|fact| fact.well_defined_fact_id == domain_requirement.well_defined_fact_id)
            .ok_or_else(|| {
                format!("checked function reduction lost domain proof {domain_index}")
            })?;
        let expected_domain = render_fact(source_fact, &source_domain_definition_context)?;
        let retained_domain = render_fact(&domain_fact.fact.proposition, context)?;
        if retained_domain != expected_domain {
            return Err(format!(
                "checked function reduction domain {domain_index} expected `{expected_domain}`, retained `{retained_domain}`"
            ));
        }
        definition_context.fact_names.insert(
            local_premise.fact_id,
            render_proof(&domain_fact.fact, context)?,
        );
        definition_context
            .fact_propositions
            .insert(local_premise.fact_id, local_premise.fact.clone());
    }
    let application_term = render_function_application(&application, context)?;
    let expected_application = render_obj(application_object, context)?;
    if expected_application != application_term {
        return Err("checked identity reduction changed its rendered equality sides".into());
    }
    let apply = if function_uses_telescope(&binding.function) {
        "Litex.fnTelescopeApplyOwn"
    } else if binding.function.domain_facts.is_empty() {
        "Litex.fnApplyOwn"
    } else {
        "Litex.fnApplyWhereOwn"
    };
    if binding.uses_native_real_body {
        let body_same =
            render_real_function_body_same_with_parameters(&binding.body, &argument_evidence)?;
        let proof = if application_side == LitexToLeanEqualitySideIr::Left {
            body_same
        } else {
            format!("Litex.Same.symm ({body_same})")
        };
        return Ok(format!(
            "(by\n  unfold {apply} {}\n  exact {proof})",
            binding.name,
        ));
    }
    let return_selection = binding
        .compatibility_return_selection
        .as_ref()
        .ok_or_else(|| {
            "native named-function binding unexpectedly requested representative selection"
                .to_string()
        })?;
    let (source_body, _, _, _) = render_function_return_selection(
        &binding.source_body,
        &return_selection.inferred_premises,
        &return_selection.return_check,
        &definition_context,
    )?;
    let other_object = match application_side {
        LitexToLeanEqualitySideIr::Left => target_right,
        LitexToLeanEqualitySideIr::Right => target_left,
    };
    let rendered_other = render_obj(other_object, context)?;
    if rendered_other != source_body {
        return Err(format!(
            "checked function reduction changed the substituted source body: expected `{source_body}`, retained `{rendered_other}`"
        ));
    }
    let proof = if application_side == LitexToLeanEqualitySideIr::Left {
        "apply Litex.Same.symm\n  apply Litex.In.same_rep"
    } else {
        "apply Litex.In.same_rep"
    };
    Ok(format!(
        "(by\n  unfold {apply} {}\n  {proof})",
        binding.name,
    ))
}

fn render_real_function_body_same_with_parameters(
    body: &LitexToLeanObjectIr,
    argument_evidence: &HashMap<SymbolId, (String, String, LitexToLeanObjectIr)>,
) -> Result<String, String> {
    match body {
        LitexToLeanObjectIr::Symbol { symbol_id, .. }
            if argument_evidence.contains_key(symbol_id) =>
        {
            let (argument, argument_membership, parameter_set) = &argument_evidence[symbol_id];
            match parameter_set {
                LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) => {
                    Ok(format!(
                        "Litex.Same.symm (Litex.In.same_rep {argument} ({argument_membership}))"
                    ))
                }
                LitexToLeanObjectIr::StandardSet(
                    LitexToLeanStandardSetIr::PositiveNatural,
                ) => {
                    let representative =
                        format!("(Litex.In.rep {argument} ({argument_membership}))");
                    Ok(format!(
                        "Litex.Same.symm (Litex.Same.trans (Litex.In.same_rep {argument} ({argument_membership})) (Litex.Same.trans (Litex.Same.subtype {representative}) (Litex.AsReal.nat ({representative}).val)))"
                    ))
                }
                other => Err(format!(
                    "checked real function reduction has no source-to-real bridge for parameter set {other:?}"
                )),
            }
        }
        LitexToLeanObjectIr::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("Litex.Same.realComplex ({normalized_value} : ℝ)"))
        }
        LitexToLeanObjectIr::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LitexToLeanBuiltinObjectOperatorIr::Add
                    | LitexToLeanBuiltinObjectOperatorIr::Sub
                    | LitexToLeanBuiltinObjectOperatorIr::Mul
                    | LitexToLeanBuiltinObjectOperatorIr::Div
            ) =>
        {
            let left =
                render_real_function_body_same_with_parameters(&arguments[0], argument_evidence)?;
            let right =
                render_real_function_body_same_with_parameters(&arguments[1], argument_evidence)?;
            let theorem = match operator {
                LitexToLeanBuiltinObjectOperatorIr::Add => "Litex.Same.realAddComplex",
                LitexToLeanBuiltinObjectOperatorIr::Sub => "Litex.Same.realSubComplex",
                LitexToLeanBuiltinObjectOperatorIr::Mul => "Litex.Same.realMulComplex",
                LitexToLeanBuiltinObjectOperatorIr::Div => "Litex.Same.realDivComplex",
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("{theorem} ({left}) ({right})"))
        }
        other => Err(format!(
            "checked real function reduction does not support body {other:?}"
        )),
    }
}

fn instantiated_predicate_components(
    source: &Fact,
    binding: &PredicateBinding,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<Vec<String>, String> {
    let definition = binding
        .definition
        .as_ref()
        .ok_or_else(|| "an abstract predicate has no reducible definition".to_string())?;
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)) = source else {
        return Err("concrete predicate component expansion requires a predicate fact".into());
    };
    if source.predicate.to_string() != definition.name
        || source.body.len() != binding.parameter_count
    {
        return Err("concrete predicate component expansion changed its application".into());
    }
    let mut nested = context.clone();
    let mut argument_index = 0;
    for group in &definition.params_def_with_type.groups {
        for parameter in &group.params {
            nested.symbol_names.insert(
                parameter.id(),
                render_obj(&source.body[argument_index], context)?,
            );
            argument_index += 1;
        }
    }
    let mut components = Vec::new();
    argument_index = 0;
    for group in &definition.params_def_with_type.groups {
        let set = parameter_set(&group.param_type)?;
        for _ in &group.params {
            let argument = render_obj(&source.body[argument_index], context)?;
            components.push(format!("Litex.In {argument} {}", render_obj(set, &nested)?));
            argument_index += 1;
        }
    }
    components.extend(
        definition
            .iff_facts
            .iter()
            .map(|fact| render_fact(fact, &nested))
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(components)
}

fn conjunction_selector(index: usize, count: usize) -> Result<String, String> {
    if count == 0 || index >= count {
        return Err("invalid conjunction projection index".into());
    }
    if count == 1 {
        return Ok(String::new());
    }
    if index == 0 {
        return Ok(".1".into());
    }
    if index == count - 1 {
        return Ok(".2".repeat(index));
    }
    Ok(format!("{}.1", ".2".repeat(index)))
}

fn render_set_builder_membership(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() {
        return Err("set-builder membership changed its checked constructor premises".into());
    }
    let (_, target_set) = membership_parts(&target.proposition)?;
    let set_builder = LitexToLeanObjectIr::lower(target_set)?;
    let LitexToLeanObjectIr::SetBuilder(builder) = set_builder else {
        return Err("set-builder membership retained a non-builder object".into());
    };
    if premises.len() != builder.facts.len() + 1 {
        return Err("set-builder membership lost its base or predicate premises".into());
    }
    let (element, _) = membership_parts(&target.proposition)?;
    let (base_element, base_set) = membership_parts(&premises[0].proposition)?;
    if obj_equality_key(element) != obj_equality_key(base_element)
        || LitexToLeanObjectIr::lower(base_set)? != *builder.set
    {
        return Err("set-builder membership changed its base-membership premise".into());
    }
    let base_proof = render_proof(&premises[0], context)?;
    let rendered_element = render_obj(element, context)?;
    let representative = format!("Litex.In.rep {rendered_element} ({base_proof})");
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(builder.symbol_id, representative.clone());

    let mut predicate_proofs = Vec::with_capacity(builder.facts.len());
    let mut source = context.clone();
    source
        .symbol_names
        .insert(builder.symbol_id, rendered_element.clone());
    let representative_same = format!("Litex.In.same_rep {rendered_element} ({base_proof})");
    for (index, fact) in builder.facts.iter().enumerate() {
        let premise = &premises[index + 1];
        if render_fact(fact, &source)? != render_fact(&premise.proposition, context)? {
            return Err(
                "set-builder predicate premise changed its checked binder substitution".into(),
            );
        }
        let source_proof = render_proof(premise, context)?;
        let proof = match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equality)) => {
                render_equality_across_representative(
                    equality,
                    &source,
                    &nested,
                    &rendered_element,
                    &representative,
                    &representative_same,
                    &source_proof,
                )?
            }
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) => {
                if predicate.body.len() != 1 {
                    return Err(
                        "set-builder concrete predicate transport requires one argument".into(),
                    );
                }
                let predicate_name = predicate.predicate.to_string();
                let binding = context
                    .predicate_bindings
                    .get(&predicate_name)
                    .ok_or_else(|| {
                        format!("unavailable concrete set-builder predicate {predicate_name}")
                    })?;
                if binding.parameter_count != 1 || binding.requirement_count != 1 {
                    return Err(
                        "set-builder concrete predicate transport requires one member parameter"
                            .into(),
                    );
                }
                let argument_source = render_obj(&predicate.body[0], &source)?;
                let argument_target = render_obj(&predicate.body[0], &nested)?;
                if argument_source != rendered_element || argument_target != representative {
                    return Err("set-builder concrete predicate changed its binder argument".into());
                }
                let definition = binding.definition.as_ref().ok_or_else(|| {
                    "abstract set-builder predicates have no transport definition".to_string()
                })?;
                let group = definition
                    .params_def_with_type
                    .groups
                    .first()
                    .ok_or_else(|| "concrete predicate lost its parameter group".to_string())?;
                let [definition_parameter] = group.params.as_slice() else {
                    return Err(
                        "set-builder concrete predicate requires one definition parameter".into(),
                    );
                };
                let set = parameter_set(&group.param_type)?;
                let component_count = binding.requirement_count + definition.iff_facts.len();
                let membership_selector = conjunction_selector(0, component_count)?;
                let rendered_set = render_obj(set, context)?;
                let mut component_proofs = vec![format!(
                    "(Litex.In.congr ({representative_same}) {rendered_set}).mp (__source{membership_selector})"
                )];
                let mut clause_source = context.clone();
                clause_source
                    .symbol_names
                    .insert(definition_parameter.id(), rendered_element.clone());
                let mut clause_target = context.clone();
                clause_target
                    .symbol_names
                    .insert(definition_parameter.id(), representative.clone());
                for (clause_index, clause) in definition.iff_facts.iter().enumerate() {
                    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = clause else {
                        return Err(
                            "set-builder concrete predicate currently transports equality clauses"
                                .into(),
                        );
                    };
                    let selector = conjunction_selector(
                        binding.requirement_count + clause_index,
                        component_count,
                    )?;
                    component_proofs.push(render_equality_across_representative(
                        equality,
                        &clause_source,
                        &clause_target,
                        &rendered_element,
                        &representative,
                        &representative_same,
                        &format!("__source{selector}"),
                    )?);
                }
                format!(
                    "(by\n  have __source := {source_proof}\n  unfold {} at __source ⊢\n  exact ⟨{}⟩)",
                    binding.lean_name,
                    component_proofs.join(", ")
                )
            }
            _ => {
                return Err(
                    "compiler set-builder membership currently transports equality clauses or one-parameter concrete predicates"
                        .into(),
                );
            }
        };
        predicate_proofs.push(proof);
    }
    let predicate_proof = if predicate_proofs.len() == 1 {
        predicate_proofs[0].clone()
    } else {
        format!("⟨{}⟩", predicate_proofs.join(", "))
    };
    Ok(format!(
        "Litex.Rules.inSetBuilder (Litex.In.same_rep {rendered_element} ({base_proof})) ({predicate_proof})"
    ))
}

fn render_equality_across_representative(
    equality: &EqualFact,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let source_left = render_obj(&equality.left, source)?;
    let source_right = render_obj(&equality.right, source)?;
    let target_left = render_obj(&equality.left, target)?;
    let target_right = render_obj(&equality.right, target)?;
    let left_changed = source_left == source_value && target_left == target_value;
    let right_changed = source_right == source_value && target_right == target_value;
    match (left_changed, right_changed) {
        (true, true) => Ok(format!("Litex.Same.refl ({target_value})")),
        (true, false) if source_right == target_right => Ok(format!(
            "Litex.Same.trans (Litex.Same.symm ({source_same_target})) ({source_proof})"
        )),
        (false, true) if source_left == target_left => Ok(format!(
            "Litex.Same.trans ({source_proof}) ({source_same_target})"
        )),
        (false, false) if source_left == target_left && source_right == target_right => {
            Ok(source_proof.into())
        }
        _ => Err(
            "compiler equality transport requires the changing value as a whole equality side"
                .into(),
        ),
    }
}

fn render_set_builder_base_membership_projection(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err("set-builder base projection changed its checked source or target".into());
    }
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    let set_builder = LitexToLeanObjectIr::lower(source_set)?;
    let LitexToLeanObjectIr::SetBuilder(builder) = set_builder else {
        return Err("set-builder base projection retained a non-builder object".into());
    };
    let (target_element, target_set) = membership_parts(&target.proposition)?;
    if obj_equality_key(source_element) != obj_equality_key(target_element)
        || LitexToLeanObjectIr::lower(target_set)? != *builder.set
    {
        return Err("set-builder base projection changed its element or base set".into());
    }
    Ok(format!(
        "Litex.Rules.inBaseOfInSetBuilder ({})",
        render_proof(&premises[0], context)?
    ))
}

#[allow(clippy::too_many_arguments)]
fn render_set_builder_predicate_projection(
    target: &LitexToLeanFactIr,
    clause_index: usize,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err("set-builder predicate projection changed its checked source or target".into());
    }
    let (_, source_set) = membership_parts(&premises[0].proposition)?;
    let set_builder = LitexToLeanObjectIr::lower(source_set)?;
    let LitexToLeanObjectIr::SetBuilder(builder) = set_builder else {
        return Err("set-builder predicate projection retained a non-builder object".into());
    };
    let clause = builder
        .facts
        .get(clause_index)
        .ok_or_else(|| "set-builder predicate projection index is out of range".to_string())?;
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = clause else {
        return Err(
            "set-builder predicate projection currently supports concrete predicates".into(),
        );
    };
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target_predicate)) = &target.proposition
    else {
        return Err("set-builder concrete predicate projected to another fact family".into());
    };
    if predicate.predicate.to_string() != target_predicate.predicate.to_string()
        || predicate.body.len() != 1
        || target_predicate.body.len() != 1
    {
        return Err("set-builder concrete predicate projection changed its application".into());
    }
    let (element, _) = membership_parts(&premises[0].proposition)?;
    let rendered_element = render_obj(element, context)?;
    let predicate_name = predicate.predicate.to_string();
    let binding = context
        .predicate_bindings
        .get(&predicate_name)
        .ok_or_else(|| format!("unavailable concrete set-builder predicate {predicate_name}"))?;
    if binding.parameter_count != 1 || binding.requirement_count != 1 {
        return Err(
            "set-builder predicate projection requires one concrete member parameter".into(),
        );
    }
    let definition = binding.definition.as_ref().ok_or_else(|| {
        "abstract set-builder predicates have no projection definition".to_string()
    })?;
    let group = definition
        .params_def_with_type
        .groups
        .first()
        .ok_or_else(|| "concrete predicate lost its parameter group".to_string())?;
    let [definition_parameter] = group.params.as_slice() else {
        return Err("set-builder concrete predicate requires one definition parameter".into());
    };
    let set = parameter_set(&group.param_type)?;
    let component_count = binding.requirement_count + definition.iff_facts.len();
    let membership_selector = conjunction_selector(0, component_count)?;
    let rendered_set = render_obj(set, context)?;
    let mut component_proofs = vec![format!(
        "(Litex.In.congr __same {rendered_set}).mpr (__selected{membership_selector})"
    )];
    let mut representative_context = context.clone();
    representative_context
        .symbol_names
        .insert(definition_parameter.id(), "__rep".into());
    let mut element_context = context.clone();
    element_context
        .symbol_names
        .insert(definition_parameter.id(), rendered_element.clone());
    for (definition_clause_index, definition_clause) in definition.iff_facts.iter().enumerate() {
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = definition_clause else {
            return Err(
                "set-builder concrete predicate projection currently transports equality clauses"
                    .into(),
            );
        };
        let selector = conjunction_selector(
            binding.requirement_count + definition_clause_index,
            component_count,
        )?;
        component_proofs.push(render_equality_across_representative(
            equality,
            &representative_context,
            &element_context,
            "__rep",
            &rendered_element,
            "Litex.Same.symm __same",
            &format!("__selected{selector}"),
        )?);
    }
    let predicate_selector = conjunction_selector(clause_index, builder.facts.len())?;
    Ok(format!(
        "(by\n  rcases Litex.Rules.inSetBuilder_iff.mp ({}) with ⟨__rep, __predicate, __same⟩\n  have __selected := __predicate{predicate_selector}\n  unfold {} at __selected ⊢\n  exact ⟨{}⟩)",
        render_proof(&premises[0], context)?,
        binding.lean_name,
        component_proofs.join(", ")
    ))
}

fn render_exist_introduction(
    target: &LitexToLeanFactIr,
    witnesses: &[Obj],
    steps: &[LitexToLeanStatementIr],
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::ExistFact(existential) = &target.proposition else {
        return Err("existential introduction targets a non-existential proposition".into());
    };
    if !existential.is_plain_exist()
        || existential.params_def_with_type().number_of_params() != 1
        || existential.facts().len() != 1
        || witnesses.len() != 1
        || parameter_requirements.len() != 1
        || premises.len() != 1
    {
        return Err(
            "compiler existential introduction supports one membership witness and one body fact"
                .into(),
        );
    }
    let group = &existential.params_def_with_type().groups[0];
    if group.params.len() != 1 {
        return Err("existential introduction requires one singleton parameter group".into());
    }
    let set = parameter_set(&group.param_type)?;
    let witness = render_obj(&witnesses[0], context)?;
    let mut instantiated = context.clone();
    instantiated
        .symbol_names
        .insert(group.params[0].id(), witness.clone());
    instantiated
        .existential_names
        .insert(group.params[0].name().to_string(), witness.clone());
    let expected_requirement = format!("Litex.In {witness} {}", render_obj(set, &instantiated)?);
    let expected_body = render_fact(
        &existential.facts()[0].from_ref_to_cloned_fact(),
        &instantiated,
    )?;
    if render_fact(&parameter_requirements[0].proposition, context)? != expected_requirement
        || render_fact(&premises[0].proposition, context)? != expected_body
    {
        return Err(
            "existential introduction witness does not instantiate its retained target facts"
                .into(),
        );
    }

    let mut nested = context.clone();
    let mut local_index = 0;
    let mut lines = vec!["by".to_string()];
    for local in render_local_statements(steps, &mut nested, "__exist_step", &mut local_index)? {
        lines.push(indent_lines(&local, 2));
    }
    let requirement_proof = render_proof(&parameter_requirements[0], &nested)?;
    let body_proof = render_proof(&premises[0], &nested)?;
    let carrier = if matches!(set, Obj::FnSet(_)) || set_requires_heterogeneous_carrier(set) {
        "_, "
    } else {
        ""
    };
    lines.push(format!(
        "  exact ⟨{carrier}{witness}, ({requirement_proof}), ({body_proof})⟩"
    ));
    Ok(format!("({})", lines.join("\n")))
}

fn render_case_split(
    target: &LitexToLeanFactIr,
    coverage: &LitexToLeanFactIr,
    branches: &[LitexToLeanCaseBranchIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::OrFact(disjunction) = &coverage.proposition else {
        return Err("case split retained non-disjunctive coverage".into());
    };
    if disjunction.facts.is_empty() || disjunction.facts.len() != branches.len() {
        return Err("case split coverage and branch counts do not match".into());
    }
    let coverage_proof = render_proof(coverage, context)?;
    let case_names = (0..branches.len())
        .map(|index| format!("__case{}", index + 1))
        .collect::<Vec<_>>();
    let mut lines = vec!["by".to_string()];
    if case_names.len() == 1 {
        let case_type = render_fact(&branches[0].assumption.fact, context)?;
        lines.push(format!(
            "  have {} : {case_type} := {coverage_proof}",
            case_names[0]
        ));
    } else {
        lines.push(format!(
            "  rcases ({coverage_proof}) with {}",
            case_names.join(" | ")
        ));
    }

    for (index, branch) in branches.iter().enumerate() {
        let expected: Fact = disjunction.facts[index].clone().into();
        if expected.to_string() != branch.assumption.fact.to_string() {
            return Err("case branch assumption changed its coverage position".into());
        }
        let mut nested = context.clone();
        nested
            .fact_names
            .insert(branch.assumption.fact_id, case_names[index].clone());
        nested
            .fact_propositions
            .insert(branch.assumption.fact_id, branch.assumption.fact.clone());
        let mut local_index = 0;
        let local_lines = render_local_proof_block(
            &branch.block,
            &mut nested,
            &format!("__case{}_step", index + 1),
            &mut local_index,
        )?;
        let exit = match &branch.exit {
            LitexToLeanCaseBranchExitIr::Conclusion(conclusion) => {
                if conclusion.fact.proposition.to_string() != target.proposition.to_string() {
                    return Err("case branch conclusion changed the exported goal".into());
                }
                crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                    &conclusion.well_definedness,
                )?;
                nested.well_definedness = Some(conclusion.well_definedness.clone());
                render_proof(&conclusion.fact, &nested)?
            }
            LitexToLeanCaseBranchExitIr::Contradiction(contradiction) => {
                format!(
                    "False.elim ({})",
                    render_contradiction(contradiction, &nested)?
                )
            }
        };
        if branches.len() == 1 {
            for local in local_lines {
                lines.push(indent_lines(&local, 2));
            }
            lines.push(format!("  exact {exit}"));
        } else {
            lines.push("  ·".into());
            for local in local_lines {
                lines.push(indent_lines(&local, 4));
            }
            lines.push(format!("    exact {exit}"));
        }
    }
    Ok(format!("({})", lines.join("\n")))
}

fn render_by_contradiction(
    target: &LitexToLeanFactIr,
    reverse_assumption: &LitexToLeanReverseAssumptionIr,
    block: &LitexToLeanLocalProofBlockIr,
    contradiction: &LitexToLeanContradictionIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(target_atomic) = &target.proposition else {
        return Err("by-contradiction currently requires an atomic target".into());
    };
    let target_is_negated = matches!(
        target_atomic,
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
    );
    let expected_introduction = if target_is_negated {
        LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation
    } else {
        LitexToLeanReverseAssumptionIntroductionIr::DirectNegation
    };
    if reverse_assumption.introduction != expected_introduction {
        return Err("by-contradiction changed target polarity".into());
    }
    let expected_reverse: Fact = target_atomic
        .logical_negation()
        .map_err(|_| "by-contradiction target has no atomic negation".to_string())?
        .into();
    if expected_reverse.to_string() != reverse_assumption.premise.fact.to_string() {
        return Err("by-contradiction reverse assumption is not the negated target".into());
    }

    let mut nested = context.clone();
    nested
        .fact_names
        .insert(reverse_assumption.premise.fact_id, "__reverse".into());
    nested.fact_propositions.insert(
        reverse_assumption.premise.fact_id,
        reverse_assumption.premise.fact.clone(),
    );
    let mut local_index = 0;
    let local_lines =
        render_local_proof_block(block, &mut nested, "__contra_step", &mut local_index)?;
    let contradiction = render_contradiction(contradiction, &nested)?;
    let mut lines = vec!["by".to_string(), "  classical".to_string()];
    match reverse_assumption.introduction {
        LitexToLeanReverseAssumptionIntroductionIr::DirectNegation => {
            lines.push("  by_contra __reverse".into());
            for local in local_lines {
                lines.push(indent_lines(&local, 2));
            }
            lines.push(format!("  exact {contradiction}"));
        }
        LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation => {
            let reverse_type = render_fact(&reverse_assumption.premise.fact, context)?;
            lines.push("  exact Classical.byContradiction (fun __negated_goal => by".into());
            lines.push(format!(
                "    have __reverse : {reverse_type} := Classical.byContradiction (fun __not_reverse => __negated_goal __not_reverse)"
            ));
            for local in local_lines {
                lines.push(indent_lines(&local, 4));
            }
            lines.push(format!("    exact {contradiction})"));
        }
    }
    Ok(format!("({})", lines.join("\n")))
}

fn render_contradiction(
    contradiction: &LitexToLeanContradictionIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(positive) = &contradiction.fact.proposition else {
        return Err("contradiction retained a non-atomic fact".into());
    };
    let expected_negation: Fact = positive
        .logical_negation()
        .map_err(|_| "contradiction fact has no atomic negation".to_string())?
        .into();
    if expected_negation.to_string() != contradiction.negated_fact.proposition.to_string() {
        return Err("contradiction facts are not logical complements".into());
    }
    let fact = render_proof(&contradiction.fact, context)?;
    let negated = render_proof(&contradiction.negated_fact, context)?;
    if matches!(positive, AtomicFact::NotEqualFact(_)) {
        let function_type = render_fact(&contradiction.fact.proposition, context)?;
        Ok(format!("(({fact} : {function_type}) ({negated}))"))
    } else {
        let function_type = render_fact(&contradiction.negated_fact.proposition, context)?;
        Ok(format!("(({negated} : {function_type}) ({fact}))"))
    }
}

fn resolve_fact_citation(
    source_fact_id: &FactId,
    expected: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let retained = context
        .fact_propositions
        .get(source_fact_id)
        .ok_or_else(|| format!("unavailable cited fact `{source_fact_id}`"))?;
    let same_proposition = if retained.to_string() == expected.to_string() {
        true
    } else if let (Fact::ForallFact(retained), Fact::ForallFact(expected)) = (retained, expected) {
        render_forall_fact_type(retained, context)? == render_forall_fact_type(expected, context)?
    } else if matches!(
        (retained, expected),
        (Fact::ExistFact(_), Fact::ExistFact(_))
    ) {
        one_witness_existentials_are_alpha_equal(retained, expected, context)?
    } else {
        false
    };
    if !same_proposition {
        return Err(format!(
            "cited FactId `{source_fact_id}` changed proposition from `{retained}` to `{expected}`"
        ));
    }
    if let Some(name) = context.fact_names.get(source_fact_id) {
        return Ok(name.clone());
    }
    let binding = context
        .forall_conclusion_bindings
        .get(source_fact_id)
        .ok_or_else(|| format!("cited FactId `{source_fact_id}` has no emitted Lean proof"))?;
    render_forall_conclusion_citation(binding, context)
}

fn render_forall_conclusion_citation(
    binding: &ForallConclusionBinding,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let parameters = binding
        .forall
        .params_def_with_type
        .collect_param_bindings_with_types();
    if parameters.len() != binding.parameter_premises.len()
        || binding.forall.dom_facts.len() != binding.premises.len()
    {
        return Err("stored forall conclusion binding changed its premise arity".into());
    }
    let mut terms = vec![binding.theorem_name.clone()];
    for ((parameter, param_type), premise) in
        parameters.iter().zip(binding.parameter_premises.iter())
    {
        let argument = context
            .symbol_names
            .get(&parameter.id())
            .cloned()
            .ok_or_else(|| {
                format!(
                    "stored forall conclusion cannot resolve parameter `{}`",
                    parameter.name()
                )
            })?;
        terms.push(argument);
        if !matches!(param_type, ParamType::Set(_)) {
            terms.push(format!(
                "({})",
                resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
            ));
        }
    }
    for premise in &binding.premises {
        terms.push(format!(
            "({})",
            resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
        ));
    }
    let application = format!("({})", terms.join(" "));
    conjunction_projection(
        &application,
        binding.conclusion_index,
        binding.conclusion_count,
    )
}

fn render_closed_standard_membership(
    fact: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(&fact.proposition)?;
    let Obj::StandardSet(set) = set else {
        return Err("closed-standard-membership certificate targets a nonstandard set".into());
    };
    if *set == StandardSet::C {
        return Ok(format!(
            "Litex.Rules.complexInC {}",
            render_obj(element, context)?
        ));
    }
    if *set == StandardSet::R {
        return render_closed_real_expression_membership(element, context);
    }
    let Obj::Number(number) = element else {
        return Err(
            "compiler closed N/Z/Q/R membership currently requires a natural numeral".into(),
        );
    };
    if number.normalized_value.is_empty()
        || !number
            .normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(
            "compiler closed N/Z/Q/R membership currently requires a natural numeral".into(),
        );
    }
    if *set == StandardSet::NPos {
        if !number
            .normalized_value
            .chars()
            .any(|character| character != '0')
        {
            return Err(
                "compiler closed N+ membership requires a strictly positive natural numeral".into(),
            );
        }
        return Ok(format!(
            "Litex.Rules.complexEqNatInNPos ({} : ℂ) {} (by norm_num) (by norm_num)",
            number.normalized_value, number.normalized_value
        ));
    }
    if *set == StandardSet::RPos {
        return Ok(format!(
            "Litex.Rules.complexEqRealInRPos ({} : ℂ) ({} : ℝ) (by norm_num) (by norm_num)",
            number.normalized_value, number.normalized_value
        ));
    }
    let theorem = match set {
        StandardSet::N => "complexEqNatInN",
        StandardSet::Z => "complexEqIntInZ",
        StandardSet::Q => "complexEqRatInQ",
        _ => return Err(format!("unsupported closed standard membership in `{set}`")),
    };
    Ok(format!(
        "Litex.Rules.{theorem} ({} : ℂ) {} (by norm_num)",
        number.normalized_value, number.normalized_value
    ))
}

fn render_closed_numeric_membership(
    fact: &LitexToLeanFactIr,
    evidence: &LitexToLeanClosedNumericMembershipProofIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_closed_numeric_membership_from_result(
        &fact.proposition,
        evidence.target_set,
        &evidence.evaluation,
        context,
    )
}

fn render_closed_numeric_membership_from_result(
    proposition: &Fact,
    evidence_target_set: StandardSet,
    evaluation: &SuccessEvaluateObjResult,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(proposition)?;
    let Obj::StandardSet(target_set) = set else {
        return Err("closed-numeric-membership certificate targets a nonstandard set".into());
    };
    if *target_set != evidence_target_set
        || obj_equality_key(element) != obj_equality_key(&evaluation.expression)
    {
        return Err(
            "closed-numeric-membership certificate changed its expression or target set".into(),
        );
    }
    let reevaluated = evaluation
        .expression
        .evaluate_to_normalized_decimal_number()
        .ok_or_else(|| "closed-numeric-membership expression no longer evaluates".to_string())?;
    if reevaluated.normalized_value != evaluation.value.normalized_value {
        return Err("closed-numeric-membership normalized value was corrupted".into());
    }
    let source = render_obj(element, context)?;
    let normalized = &evaluation.value.normalized_value;
    match target_set {
        StandardSet::C => Ok(format!("Litex.Rules.complexInC {source}")),
        StandardSet::N
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInN {source} {normalized} (by norm_num)"
            ))
        }
        StandardSet::NPos
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit())
                && normalized.chars().any(|character| character != '0') =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInNPos {source} {normalized} (by norm_num) (by norm_num)"
            ))
        }
        StandardSet::Z => Ok(format!(
            "Litex.Rules.complexEqIntInZ {source} {normalized} (by norm_num)"
        )),
        StandardSet::Q => Ok(format!(
            "Litex.Rules.complexEqRatInQ {source} {normalized} (by norm_num)"
        )),
        StandardSet::R => render_closed_real_expression_membership(element, context),
        StandardSet::RPos => Ok(format!(
            "Litex.Rules.complexEqRealInRPos {source} ({normalized} : ℝ) (by norm_num) (by norm_num)"
        )),
        _ => Err(format!(
            "unsupported closed numeric membership in `{target_set}` with value `{normalized}`"
        )),
    }
}

fn render_closed_real_expression_membership(
    element: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right, theorem) = match element {
        Obj::Add(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInR",
        ),
        Obj::Sub(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInR",
        ),
        Obj::Mul(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInR",
        ),
        Obj::Div(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInR",
        ),
        Obj::Number(number) => {
            if number.normalized_value.parse::<i128>().is_err() {
                return Err(
                    "closed real-expression membership requires integral numeral leaves".into(),
                );
            }
            return Ok(format!(
                "Litex.Rules.complexRealInR ({} : ℝ)",
                number.normalized_value
            ));
        }
        _ => {
            return Err(format!(
                "closed real-expression membership has unsupported operand `{element}`"
            ));
        }
    };
    render_obj(element, context)?;
    Ok(format!(
        "Litex.Rules.{theorem} ({}) ({})",
        render_closed_real_expression_membership(left, context)?,
        render_closed_real_expression_membership(right, context)?
    ))
}

fn render_closed_numeric_comparison(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty()
        || !premises.is_empty()
        || !crate::litex_to_lean_ir::is_closed_numeric_relation(&fact.proposition)
    {
        return Err(
            "closed numeric comparison changed its target or retained unexpected premises".into(),
        );
    }
    render_closed_numeric_comparison_fact(&fact.proposition, context)
}

fn render_closed_numeric_comparison_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !crate::litex_to_lean_ir::is_closed_numeric_relation(fact) {
        return Err("closed numeric comparison changed its target".into());
    }
    let (left, right, theorem, strict, negated) = match fact {
        Fact::AtomicFact(AtomicFact::LessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::LessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::NotLessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotLessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, true)
        }
        _ => {
            return Err(
                "compiler closed comparison requires an order relation; closed equality and disequality use separate semantic adapters"
                    .into()
            )
        }
    };
    render_obj(left, context)?;
    render_obj(right, context)?;
    if negated {
        return Ok("(by\n  norm_num [Litex.Lt, Litex.Le, Litex.OrderValue])".into());
    }
    if left.to_string() == "0" {
        let theorem = if strict {
            "positiveOfComplexReal"
        } else {
            "nonnegativeOfComplexReal"
        };
        return Ok(format!("Litex.OrderBridge.{theorem} (by norm_num)"));
    }
    Ok(format!("Litex.OrderBridge.{theorem} (by norm_num)"))
}

fn render_number_theory_reflection(
    fact: &LitexToLeanFactIr,
    rule: &LitexToLeanBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("number-theory reflection retained unexpected child proofs".into());
    }
    let (predicate, arguments, negated) = match &fact.proposition {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(value)) => {
            (value.predicate.to_string(), value.body.as_slice(), false)
        }
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(value)) => {
            (value.predicate.to_string(), value.body.as_slice(), true)
        }
        _ => return Err("number-theory reflection retained a non-predicate target".into()),
    };
    let (expected_predicate, expected_arity) = match rule {
        LitexToLeanBuiltinRuleIr::PrimeU64Reflection => (PRIME, 1),
        LitexToLeanBuiltinRuleIr::CoprimeNaturalReflection => (COPRIME, 2),
        _ => return Err("non-reflection rule reached number-theory renderer".into()),
    };
    if predicate != expected_predicate || arguments.len() != expected_arity {
        return Err("number-theory reflection changed its predicate or arity".into());
    }
    for argument in arguments {
        let Obj::Number(number) = argument else {
            return Err("number-theory reflection changed a closed numeric argument".into());
        };
        if number.normalized_value.starts_with('-') || number.normalized_value.contains('.') {
            return Err("number-theory reflection retained a non-natural argument".into());
        }
        if matches!(rule, LitexToLeanBuiltinRuleIr::PrimeU64Reflection)
            && number.normalized_value.parse::<u64>().is_err()
        {
            return Err("prime reflection retained a value outside its u64 certificate".into());
        }
    }
    render_fact(&fact.proposition, context)?;
    let values = arguments
        .iter()
        .map(|argument| match argument {
            Obj::Number(number) => Ok(number.normalized_value.as_str()),
            _ => Err("number-theory reflection changed a numeric argument".to_string()),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(match rule {
        LitexToLeanBuiltinRuleIr::PrimeU64Reflection => {
            let theorem = if negated {
                "notPrimeOfNat"
            } else {
                "primeOfNat"
            };
            format!(
                "(by simpa using (Litex.{theorem} {} (by norm_num)))",
                values[0]
            )
        }
        LitexToLeanBuiltinRuleIr::CoprimeNaturalReflection => {
            let theorem = if negated {
                "notCoprimeOfNat"
            } else {
                "coprimeOfNat"
            };
            format!(
                "(by simpa using (Litex.{theorem} {} {} (by norm_num)))",
                values[0], values[1]
            )
        }
        _ => unreachable!("validated reflection rule"),
    })
}

fn render_not_equal_symmetry(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "not-equality symmetry requires one premise and no parameter requirements".into(),
        );
    }
    let (target_left, target_right) = not_equal_parts(&fact.proposition)?;
    let (source_left, source_right) = not_equal_parts(&premises[0].proposition)?;
    if obj_equality_key(source_left) != obj_equality_key(target_right)
        || obj_equality_key(source_right) != obj_equality_key(target_left)
    {
        return Err("not-equality symmetry premise does not reverse the target objects".into());
    }
    Ok(format!(
        "Litex.Rules.notSameSymm ({})",
        render_proof(&premises[0], context)?
    ))
}

fn standard_set_membership_projection_theorem_chain(
    source_set: StandardSet,
    target_set: StandardSet,
) -> Result<&'static [&'static str], String> {
    match (source_set, target_set) {
        (StandardSet::NPos, StandardSet::N) => Ok(&["inNOfInNPos"]),
        (StandardSet::NPos, StandardSet::Z) => Ok(&["inNOfInNPos", "inZOfInN"]),
        (StandardSet::NPos, StandardSet::Q) => Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ"]),
        (StandardSet::NPos, StandardSet::R) => {
            Ok(&["inNOfInNPos", "inZOfInN", "inQOfInZ", "inROfInQ"])
        }
        (StandardSet::NPos, StandardSet::C) => Ok(&[
            "inNOfInNPos",
            "inZOfInN",
            "inQOfInZ",
            "inROfInQ",
            "inCOfInR",
        ]),
        (StandardSet::RPos, StandardSet::R) => Ok(&["inROfInRPos"]),
        (StandardSet::RPos, StandardSet::C) => Ok(&["inROfInRPos", "inCOfInR"]),
        (StandardSet::ZStar, StandardSet::Z) => Ok(&["inZOfInZStar"]),
        (StandardSet::ZStar, StandardSet::Q) => Ok(&["inZOfInZStar", "inQOfInZ"]),
        (StandardSet::ZStar, StandardSet::R) => Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ"]),
        (StandardSet::ZStar, StandardSet::C) => {
            Ok(&["inZOfInZStar", "inQOfInZ", "inROfInQ", "inCOfInR"])
        }
        (StandardSet::QStar, StandardSet::Q) => Ok(&["inQOfInQStar"]),
        (StandardSet::QStar, StandardSet::R) => Ok(&["inQOfInQStar", "inROfInQ"]),
        (StandardSet::QStar, StandardSet::C) => Ok(&["inQOfInQStar", "inROfInQ", "inCOfInR"]),
        (StandardSet::RStar, StandardSet::R) => Ok(&["inROfInRStar"]),
        (StandardSet::RStar, StandardSet::C) => Ok(&["inROfInRStar", "inCOfInR"]),
        (StandardSet::CStar, StandardSet::C) => Ok(&["inCOfInCStar"]),
        (StandardSet::ZStar, StandardSet::QStar) => Ok(&["inQStarOfInZStar"]),
        (StandardSet::ZStar, StandardSet::RStar) => Ok(&["inQStarOfInZStar", "inRStarOfInQStar"]),
        (StandardSet::ZStar, StandardSet::CStar) => {
            Ok(&["inQStarOfInZStar", "inRStarOfInQStar", "inCStarOfInRStar"])
        }
        (StandardSet::QStar, StandardSet::RStar) => Ok(&["inRStarOfInQStar"]),
        (StandardSet::QStar, StandardSet::CStar) => Ok(&["inRStarOfInQStar", "inCStarOfInRStar"]),
        (StandardSet::RStar, StandardSet::CStar) => Ok(&["inCStarOfInRStar"]),
        (StandardSet::N, StandardSet::Z) => Ok(&["inZOfInN"]),
        (StandardSet::N, StandardSet::Q) => Ok(&["inZOfInN", "inQOfInZ"]),
        (StandardSet::N, StandardSet::R) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ"]),
        (StandardSet::N, StandardSet::C) => Ok(&["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Z, StandardSet::Q) => Ok(&["inQOfInZ"]),
        (StandardSet::Z, StandardSet::R) => Ok(&["inQOfInZ", "inROfInQ"]),
        (StandardSet::Z, StandardSet::C) => Ok(&["inQOfInZ", "inROfInQ", "inCOfInR"]),
        (StandardSet::Q, StandardSet::R) => Ok(&["inROfInQ"]),
        (StandardSet::Q, StandardSet::C) => Ok(&["inROfInQ", "inCOfInR"]),
        (StandardSet::R, StandardSet::C) => Ok(&["inCOfInR"]),
        _ => Err(format!(
            "unsupported standard-set membership projection `{source_set}` to `{target_set}`"
        )),
    }
}

fn render_standard_set_membership_projection(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "standard-set membership projection requires one premise and no parameter requirements"
                .into(),
        );
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    if obj_equality_key(target_element) != obj_equality_key(source_element) {
        return Err("standard-set membership projection changed its source element".into());
    }
    let (Obj::StandardSet(source_set), Obj::StandardSet(target_set)) = (source_set, target_set)
    else {
        return Err("standard-set membership projection retained a nonstandard set".into());
    };
    let theorem_chain = standard_set_membership_projection_theorem_chain(*source_set, *target_set)?;
    let mut proof = render_proof(&premises[0], context)?;
    for theorem in theorem_chain {
        proof = format!("Litex.Rules.{theorem} ({proof})");
    }
    Ok(proof)
}

fn render_standard_set_subset(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("standard-set subset requires no retained premises".into());
    }
    let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = &fact.proposition else {
        return Err("standard-set subset evidence retained a non-subset target".into());
    };
    let (Obj::StandardSet(source), Obj::StandardSet(target)) = (&subset.left, &subset.right) else {
        return Err("standard-set subset evidence retained a nonstandard endpoint".into());
    };
    render_fact(&fact.proposition, context)?;
    if source == target {
        return Ok("(fun _x hx => hx)".into());
    }
    let theorem_chain: &[&str] = match (source, target) {
        (StandardSet::NPos, StandardSet::N) => &["inNOfInNPos"],
        (StandardSet::RPos, StandardSet::R) => &["inROfInRPos"],
        (StandardSet::RPos, StandardSet::C) => &["inROfInRPos", "inCOfInR"],
        (StandardSet::ZStar, StandardSet::Z) => &["inZOfInZStar"],
        (StandardSet::ZStar, StandardSet::Q) => &["inZOfInZStar", "inQOfInZ"],
        (StandardSet::ZStar, StandardSet::R) => &["inZOfInZStar", "inQOfInZ", "inROfInQ"],
        (StandardSet::ZStar, StandardSet::C) => {
            &["inZOfInZStar", "inQOfInZ", "inROfInQ", "inCOfInR"]
        }
        (StandardSet::QStar, StandardSet::Q) => &["inQOfInQStar"],
        (StandardSet::QStar, StandardSet::R) => &["inQOfInQStar", "inROfInQ"],
        (StandardSet::QStar, StandardSet::C) => &["inQOfInQStar", "inROfInQ", "inCOfInR"],
        (StandardSet::RStar, StandardSet::R) => &["inROfInRStar"],
        (StandardSet::RStar, StandardSet::C) => &["inROfInRStar", "inCOfInR"],
        (StandardSet::CStar, StandardSet::C) => &["inCOfInCStar"],
        (StandardSet::ZStar, StandardSet::QStar) => &["inQStarOfInZStar"],
        (StandardSet::ZStar, StandardSet::RStar) => &["inQStarOfInZStar", "inRStarOfInQStar"],
        (StandardSet::ZStar, StandardSet::CStar) => {
            &["inQStarOfInZStar", "inRStarOfInQStar", "inCStarOfInRStar"]
        }
        (StandardSet::QStar, StandardSet::RStar) => &["inRStarOfInQStar"],
        (StandardSet::QStar, StandardSet::CStar) => &["inRStarOfInQStar", "inCStarOfInRStar"],
        (StandardSet::RStar, StandardSet::CStar) => &["inCStarOfInRStar"],
        (StandardSet::N, StandardSet::Z) => &["inZOfInN"],
        (StandardSet::N, StandardSet::Q) => &["inZOfInN", "inQOfInZ"],
        (StandardSet::N, StandardSet::R) => &["inZOfInN", "inQOfInZ", "inROfInQ"],
        (StandardSet::N, StandardSet::C) => &["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"],
        (StandardSet::Z, StandardSet::Q) => &["inQOfInZ"],
        (StandardSet::Z, StandardSet::R) => &["inQOfInZ", "inROfInQ"],
        (StandardSet::Z, StandardSet::C) => &["inQOfInZ", "inROfInQ", "inCOfInR"],
        (StandardSet::Q, StandardSet::R) => &["inROfInQ"],
        (StandardSet::Q, StandardSet::C) => &["inROfInQ", "inCOfInR"],
        (StandardSet::R, StandardSet::C) => &["inCOfInR"],
        _ => {
            return Err(format!(
                "unsupported standard-set subset `{source}` to `{target}`"
            ));
        }
    };
    let mut proof = "hx".to_string();
    for theorem in theorem_chain {
        proof = format!("Litex.Rules.{theorem} ({proof})");
    }
    Ok(format!("(fun _x hx => {proof})"))
}

fn render_finite_set_constructor(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanFiniteSetBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("finite-set constructor reflection requires no retained premises".into());
    }
    let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(target)) = &fact.proposition else {
        return Err("finite-set reflection retained a non-finiteness target".into());
    };
    render_fact(&fact.proposition, context)?;
    match (rule, &target.set) {
        (LitexToLeanFiniteSetBuiltinRuleIr::Range, Obj::Range(_)) => {
            Ok("(by unfold Litex.Set.Finite Litex.range; infer_instance)".into())
        }
        (LitexToLeanFiniteSetBuiltinRuleIr::ClosedRange, Obj::ClosedRange(_)) => {
            Ok("(by unfold Litex.Set.Finite Litex.closedRange; infer_instance)".into())
        }
        (LitexToLeanFiniteSetBuiltinRuleIr::ListSet, Obj::ListSet(list_set)) => {
            render_list_set_finiteness(
                &list_set
                    .list
                    .iter()
                    .map(|item| LitexToLeanObjectIr::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
                context,
            )
        }
        _ => Err("finite-set reflection changed its exact constructor family".into()),
    }
}

fn render_set_builtin_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanSetBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() {
        return Err("set builtin retained unexpected parameter requirements".into());
    }
    match rule {
        LitexToLeanSetBuiltinRuleIr::UnionCommutative
        | LitexToLeanSetBuiltinRuleIr::UnionAssociative
        | LitexToLeanSetBuiltinRuleIr::UnionIdempotent
        | LitexToLeanSetBuiltinRuleIr::UnionEmptyIdentity
        | LitexToLeanSetBuiltinRuleIr::IntersectCommutative
        | LitexToLeanSetBuiltinRuleIr::IntersectAssociative => {
            if !premises.is_empty() {
                return Err("structural set equality unexpectedly retained premises".into());
            }
            render_structural_set_equality(fact, rule, context)
        }
        LitexToLeanSetBuiltinRuleIr::UnionMembershipLeft
        | LitexToLeanSetBuiltinRuleIr::UnionMembershipRight => {
            if premises.len() != 1 {
                return Err("union membership requires one selected side premise".into());
            }
            let (element, target_set) = membership_parts(&fact.proposition)?;
            let Obj::Union(union) = target_set else {
                return Err("union membership certificate targets another constructor".into());
            };
            let expected_side = if rule == LitexToLeanSetBuiltinRuleIr::UnionMembershipLeft {
                union.left.as_ref()
            } else {
                union.right.as_ref()
            };
            let (premise_element, premise_set) = membership_parts(&premises[0].proposition)?;
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(expected_side) != obj_equality_key(premise_set)
            {
                return Err("union membership changed its selected side or element".into());
            }
            let theorem = if rule == LitexToLeanSetBuiltinRuleIr::UnionMembershipLeft {
                "inUnionLeft"
            } else {
                "inUnionRight"
            };
            render_fact(&fact.proposition, context)?;
            Ok(format!(
                "Litex.SetRules.{theorem} ({})",
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectMembershipBoth => {
            if premises.len() != 2 {
                return Err("intersection membership requires two ordered side premises".into());
            }
            let (element, target_set) = membership_parts(&fact.proposition)?;
            let Obj::Intersect(intersection) = target_set else {
                return Err(
                    "intersection membership certificate targets another constructor".into(),
                );
            };
            for (premise, expected_set) in premises
                .iter()
                .zip([intersection.left.as_ref(), intersection.right.as_ref()])
            {
                let (premise_element, premise_set) = membership_parts(&premise.proposition)?;
                if obj_equality_key(element) != obj_equality_key(premise_element)
                    || obj_equality_key(expected_set) != obj_equality_key(premise_set)
                {
                    return Err("intersection membership changed its ordered side premises".into());
                }
            }
            render_fact(&fact.proposition, context)?;
            Ok(format!(
                "Litex.SetRules.inIntersect ({}) ({})",
                render_proof(&premises[0], context)?,
                render_proof(&premises[1], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipLeft
        | LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipRight => {
            if premises.len() != 1 {
                return Err(
                    "intersection non-membership requires one selected side premise".into(),
                );
            }
            let (element, target_set) = nonmembership_parts(&fact.proposition)?;
            let Obj::Intersect(intersection) = target_set else {
                return Err(
                    "intersection non-membership certificate targets another constructor".into(),
                );
            };
            let expected_side = if rule == LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipLeft {
                intersection.left.as_ref()
            } else {
                intersection.right.as_ref()
            };
            let (premise_element, premise_set) = nonmembership_parts(&premises[0].proposition)?;
            if obj_equality_key(element) != obj_equality_key(premise_element)
                || obj_equality_key(expected_side) != obj_equality_key(premise_set)
            {
                return Err("intersection non-membership changed its selected side".into());
            }
            let theorem = if rule == LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipLeft {
                "notInIntersectOfNotInLeft"
            } else {
                "notInIntersectOfNotInRight"
            };
            render_fact(&fact.proposition, context)?;
            Ok(format!(
                "Litex.SetRules.{theorem} ({})",
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::SetMinusMembership => {
            if premises.len() != 2 {
                return Err(
                    "set-minus membership requires left membership and right non-membership".into(),
                );
            }
            let (element, target_set) = membership_parts(&fact.proposition)?;
            let Obj::SetMinus(difference) = target_set else {
                return Err("set-minus membership certificate targets another constructor".into());
            };
            let (left_element, left_set) = membership_parts(&premises[0].proposition)?;
            let (right_element, right_set) = nonmembership_parts(&premises[1].proposition)?;
            if obj_equality_key(element) != obj_equality_key(left_element)
                || obj_equality_key(element) != obj_equality_key(right_element)
                || obj_equality_key(difference.left.as_ref()) != obj_equality_key(left_set)
                || obj_equality_key(difference.right.as_ref()) != obj_equality_key(right_set)
            {
                return Err("set-minus membership changed its ordered premises".into());
            }
            render_fact(&fact.proposition, context)?;
            Ok(format!(
                "Litex.SetRules.inSetMinus ({}) ({})",
                render_proof(&premises[0], context)?,
                render_proof(&premises[1], context)?
            ))
        }
        rule @ (LitexToLeanSetBuiltinRuleIr::EmptySubset
        | LitexToLeanSetBuiltinRuleIr::IntersectEqLeftOfSubset
        | LitexToLeanSetBuiltinRuleIr::IntersectEqRightOfSubset
        | LitexToLeanSetBuiltinRuleIr::IntersectFinite
        | LitexToLeanSetBuiltinRuleIr::IntersectSubsetLeft
        | LitexToLeanSetBuiltinRuleIr::IntersectSubsetRight
        | LitexToLeanSetBuiltinRuleIr::IntersectUnionDistributive
        | LitexToLeanSetBuiltinRuleIr::PowerSetFinite
        | LitexToLeanSetBuiltinRuleIr::PowerSetMembershipOfSubset
        | LitexToLeanSetBuiltinRuleIr::PowerSetNonempty
        | LitexToLeanSetBuiltinRuleIr::SetMinusFiniteLeft
        | LitexToLeanSetBuiltinRuleIr::SetMinusIntersectDeMorgan
        | LitexToLeanSetBuiltinRuleIr::SetMinusRecoverSubset
        | LitexToLeanSetBuiltinRuleIr::SetMinusSubsetLeft
        | LitexToLeanSetBuiltinRuleIr::SetMinusUnionDeMorgan
        | LitexToLeanSetBuiltinRuleIr::SubsetEqSetMinusRecovery
        | LitexToLeanSetBuiltinRuleIr::SubsetUnionLeft
        | LitexToLeanSetBuiltinRuleIr::SubsetUnionRight
        | LitexToLeanSetBuiltinRuleIr::UnionFinite
        | LitexToLeanSetBuiltinRuleIr::UnionNonemptyLeft
        | LitexToLeanSetBuiltinRuleIr::UnionNonemptyRight
        | LitexToLeanSetBuiltinRuleIr::UnionSubset) => {
            render_extended_set_rule(fact, rule, premises, context)
        }
    }
}

fn render_extended_set_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanSetBuiltinRuleIr,
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_fact(&fact.proposition, context)?;
    match rule {
        LitexToLeanSetBuiltinRuleIr::EmptySubset => {
            if !premises.is_empty() {
                return Err("empty-subset rule retained premises".into());
            }
            let (empty, target) = subset_parts(&fact.proposition)?;
            if !matches!(empty, Obj::ListSet(set) if set.list.is_empty()) {
                return Err("empty-subset rule changed its empty left endpoint".into());
            }
            Ok(format!(
                "Litex.SetRules.emptySubset {}",
                render_obj(target, context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::SubsetUnionLeft
        | LitexToLeanSetBuiltinRuleIr::SubsetUnionRight => {
            if !premises.is_empty() {
                return Err("subset-union inclusion retained premises".into());
            }
            let (source, target) = subset_parts(&fact.proposition)?;
            let Obj::Union(union) = target else {
                return Err("subset-union inclusion changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LitexToLeanSetBuiltinRuleIr::SubsetUnionLeft {
                (union.left.as_ref(), "subsetUnionLeft")
            } else {
                (union.right.as_ref(), "subsetUnionRight")
            };
            if obj_equality_key(source) != obj_equality_key(expected) {
                return Err("subset-union inclusion changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::UnionSubset => {
            if premises.len() != 2 {
                return Err("union-subset rule requires two ordered subset premises".into());
            }
            let (source, target) = subset_parts(&fact.proposition)?;
            let Obj::Union(union) = source else {
                return Err("union-subset rule changed its source constructor".into());
            };
            for (premise, operand) in premises.iter().zip([&union.left, &union.right]) {
                let (premise_source, premise_target) = subset_parts(&premise.proposition)?;
                if obj_equality_key(premise_source) != obj_equality_key(operand.as_ref())
                    || obj_equality_key(premise_target) != obj_equality_key(target)
                {
                    return Err("union-subset rule changed its ordered premises".into());
                }
            }
            Ok(format!(
                "Litex.SetRules.unionSubset ({}) ({})",
                render_proof(&premises[0], context)?,
                render_proof(&premises[1], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectSubsetLeft
        | LitexToLeanSetBuiltinRuleIr::IntersectSubsetRight
        | LitexToLeanSetBuiltinRuleIr::SetMinusSubsetLeft => {
            if !premises.is_empty() {
                return Err("constructor-subset rule retained premises".into());
            }
            let (source, target) = subset_parts(&fact.proposition)?;
            let (left, right, expected, theorem) = match (rule, source) {
                (LitexToLeanSetBuiltinRuleIr::IntersectSubsetLeft, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "intersectSubsetLeft",
                ),
                (LitexToLeanSetBuiltinRuleIr::IntersectSubsetRight, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.right.as_ref(),
                    "intersectSubsetRight",
                ),
                (LitexToLeanSetBuiltinRuleIr::SetMinusSubsetLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    value.left.as_ref(),
                    "setMinusSubsetLeft",
                ),
                _ => return Err("constructor-subset rule changed its constructor".into()),
            };
            if obj_equality_key(target) != obj_equality_key(expected) {
                return Err("constructor-subset rule changed its projected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {}",
                render_obj(left, context)?,
                render_obj(right, context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::UnionFinite
        | LitexToLeanSetBuiltinRuleIr::IntersectFinite
        | LitexToLeanSetBuiltinRuleIr::SetMinusFiniteLeft => {
            let target = finite_set_parts(&fact.proposition)?;
            let (left, right, theorem, expected_premises) = match (rule, target) {
                (LitexToLeanSetBuiltinRuleIr::UnionFinite, Obj::Union(value)) => {
                    (value.left.as_ref(), value.right.as_ref(), "unionFinite", 2)
                }
                (LitexToLeanSetBuiltinRuleIr::IntersectFinite, Obj::Intersect(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "intersectFinite",
                    2,
                ),
                (LitexToLeanSetBuiltinRuleIr::SetMinusFiniteLeft, Obj::SetMinus(value)) => (
                    value.left.as_ref(),
                    value.right.as_ref(),
                    "setMinusFiniteLeft",
                    1,
                ),
                _ => return Err("finite-set rule changed its target constructor".into()),
            };
            if premises.len() != expected_premises
                || obj_equality_key(finite_set_parts(&premises[0].proposition)?)
                    != obj_equality_key(left)
                || (expected_premises == 2
                    && obj_equality_key(finite_set_parts(&premises[1].proposition)?)
                        != obj_equality_key(right))
            {
                return Err("finite-set rule changed its ordered finiteness premises".into());
            }
            let mut terms = vec![
                format!("Litex.SetRules.{theorem}"),
                render_obj(left, context)?,
                render_obj(right, context)?,
                format!("({})", render_proof(&premises[0], context)?),
            ];
            if expected_premises == 2 && rule == LitexToLeanSetBuiltinRuleIr::UnionFinite {
                terms.push(format!("({})", render_proof(&premises[1], context)?));
            }
            Ok(terms.join(" "))
        }
        LitexToLeanSetBuiltinRuleIr::UnionNonemptyLeft
        | LitexToLeanSetBuiltinRuleIr::UnionNonemptyRight => {
            if premises.len() != 1 {
                return Err("union nonemptiness requires one selected premise".into());
            }
            let target = nonempty_set_parts(&fact.proposition)?;
            let Obj::Union(union) = target else {
                return Err("union nonemptiness changed its target constructor".into());
            };
            let (expected, theorem) = if rule == LitexToLeanSetBuiltinRuleIr::UnionNonemptyLeft {
                (union.left.as_ref(), "unionNonemptyLeft")
            } else {
                (union.right.as_ref(), "unionNonemptyRight")
            };
            if obj_equality_key(nonempty_set_parts(&premises[0].proposition)?)
                != obj_equality_key(expected)
            {
                return Err("union nonemptiness changed its selected operand".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} {} {} ({})",
                render_obj(union.left.as_ref(), context)?,
                render_obj(union.right.as_ref(), context)?,
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::PowerSetMembershipOfSubset => {
            if premises.len() != 1 {
                return Err("power-set membership requires one subset premise".into());
            }
            let (subset, target) = membership_parts(&fact.proposition)?;
            let Obj::PowerSet(power) = target else {
                return Err("power-set membership changed its target constructor".into());
            };
            let (premise_subset, premise_base) = subset_parts(&premises[0].proposition)?;
            if obj_equality_key(subset) != obj_equality_key(premise_subset)
                || obj_equality_key(power.set.as_ref()) != obj_equality_key(premise_base)
            {
                return Err("power-set membership changed its subset endpoints".into());
            }
            Ok(format!(
                "Litex.SetRules.inPowerSetOfSubset ({})",
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::PowerSetNonempty => {
            if !premises.is_empty() {
                return Err("power-set nonemptiness retained premises".into());
            }
            let Obj::PowerSet(power) = nonempty_set_parts(&fact.proposition)? else {
                return Err("power-set nonemptiness changed its constructor".into());
            };
            Ok(format!(
                "Litex.SetRules.powerSetNonempty {}",
                render_obj(power.set.as_ref(), context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::PowerSetFinite => {
            if premises.len() != 1 {
                return Err("power-set finiteness requires one base finiteness premise".into());
            }
            let Obj::PowerSet(power) = finite_set_parts(&fact.proposition)? else {
                return Err("power-set finiteness changed its constructor".into());
            };
            if obj_equality_key(finite_set_parts(&premises[0].proposition)?)
                != obj_equality_key(power.set.as_ref())
            {
                return Err("power-set finiteness changed its base premise".into());
            }
            Ok(format!(
                "Litex.SetRules.powerSetFinite {} ({})",
                render_obj(power.set.as_ref(), context)?,
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectEqLeftOfSubset
        | LitexToLeanSetBuiltinRuleIr::IntersectEqRightOfSubset => {
            if premises.len() != 1 {
                return Err("intersection absorption requires one subset premise".into());
            }
            let (left, right) = equality_parts(&fact.proposition)?;
            let Obj::Intersect(intersection) = left else {
                return Err("intersection absorption changed its equality constructor".into());
            };
            let (premise_left, premise_right) = subset_parts(&premises[0].proposition)?;
            let (expected_result, expected_left, expected_right, theorem) =
                if rule == LitexToLeanSetBuiltinRuleIr::IntersectEqLeftOfSubset {
                    (
                        intersection.left.as_ref(),
                        intersection.left.as_ref(),
                        intersection.right.as_ref(),
                        "intersectEqLeftOfSubset",
                    )
                } else {
                    (
                        intersection.right.as_ref(),
                        intersection.right.as_ref(),
                        intersection.left.as_ref(),
                        "intersectEqRightOfSubset",
                    )
                };
            if obj_equality_key(right) != obj_equality_key(expected_result)
                || obj_equality_key(premise_left) != obj_equality_key(expected_left)
                || obj_equality_key(premise_right) != obj_equality_key(expected_right)
            {
                return Err("intersection absorption changed its operands".into());
            }
            Ok(format!(
                "Litex.SetRules.{theorem} ({})",
                render_proof(&premises[0], context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectUnionDistributive
        | LitexToLeanSetBuiltinRuleIr::SetMinusIntersectDeMorgan
        | LitexToLeanSetBuiltinRuleIr::SetMinusUnionDeMorgan => {
            if !premises.is_empty() {
                return Err("structural three-set equality retained premises".into());
            }
            render_three_set_equality(fact, rule, context)
        }
        LitexToLeanSetBuiltinRuleIr::SetMinusRecoverSubset
        | LitexToLeanSetBuiltinRuleIr::SubsetEqSetMinusRecovery => {
            if premises.len() != 1 {
                return Err("set-minus recovery requires one subset premise".into());
            }
            let (subset, left) = subset_parts(&premises[0].proposition)?;
            let (equality_left, equality_right) = equality_parts(&fact.proposition)?;
            let (difference, plain, reverse) =
                if rule == LitexToLeanSetBuiltinRuleIr::SetMinusRecoverSubset {
                    (equality_left, equality_right, false)
                } else {
                    (equality_right, equality_left, true)
                };
            let Obj::SetMinus(outer) = difference else {
                return Err("set-minus recovery changed its outer constructor".into());
            };
            let Obj::SetMinus(inner) = outer.right.as_ref() else {
                return Err("set-minus recovery changed its inner constructor".into());
            };
            if obj_equality_key(plain) != obj_equality_key(subset)
                || obj_equality_key(outer.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.left.as_ref()) != obj_equality_key(left)
                || obj_equality_key(inner.right.as_ref()) != obj_equality_key(subset)
            {
                return Err("set-minus recovery changed its subset operands".into());
            }
            let proof = format!(
                "Litex.SetRules.setMinusRecoverSubset ({})",
                render_proof(&premises[0], context)?
            );
            Ok(if reverse {
                format!("Litex.Same.symm ({proof})")
            } else {
                proof
            })
        }
        _ => Err("base set rule reached extended set-rule renderer".into()),
    }
}

fn render_three_set_equality(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanSetBuiltinRuleIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(&fact.proposition)?;
    let (first, second, third, theorem) = match rule {
        LitexToLeanSetBuiltinRuleIr::IntersectUnionDistributive => {
            let Obj::Intersect(left_intersection) = left else {
                return Err("intersection distributivity changed its left constructor".into());
            };
            let Obj::Union(left_union) = left_intersection.right.as_ref() else {
                return Err("intersection distributivity changed its inner union".into());
            };
            let Obj::Union(right_union) = right else {
                return Err("intersection distributivity changed its right constructor".into());
            };
            let (Obj::Intersect(right_left), Obj::Intersect(right_right)) =
                (right_union.left.as_ref(), right_union.right.as_ref())
            else {
                return Err("intersection distributivity changed its result intersections".into());
            };
            let first = left_intersection.left.as_ref();
            let second = left_union.left.as_ref();
            let third = left_union.right.as_ref();
            if obj_equality_key(right_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(right_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(right_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection distributivity changed its repeated operands".into());
            }
            (first, second, third, "intersectUnionDistributive")
        }
        LitexToLeanSetBuiltinRuleIr::SetMinusIntersectDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("intersection De Morgan changed its left difference".into());
            };
            let Obj::Intersect(excluded) = left_difference.right.as_ref() else {
                return Err("intersection De Morgan changed its excluded intersection".into());
            };
            let Obj::Union(result) = right else {
                return Err("intersection De Morgan changed its result union".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("intersection De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("intersection De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusIntersectDeMorgan")
        }
        LitexToLeanSetBuiltinRuleIr::SetMinusUnionDeMorgan => {
            let Obj::SetMinus(left_difference) = left else {
                return Err("union De Morgan changed its left difference".into());
            };
            let Obj::Union(excluded) = left_difference.right.as_ref() else {
                return Err("union De Morgan changed its excluded union".into());
            };
            let Obj::Intersect(result) = right else {
                return Err("union De Morgan changed its result intersection".into());
            };
            let (Obj::SetMinus(result_left), Obj::SetMinus(result_right)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return Err("union De Morgan changed its result differences".into());
            };
            let first = left_difference.left.as_ref();
            let second = excluded.left.as_ref();
            let third = excluded.right.as_ref();
            if obj_equality_key(result_left.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_left.right.as_ref()) != obj_equality_key(second)
                || obj_equality_key(result_right.left.as_ref()) != obj_equality_key(first)
                || obj_equality_key(result_right.right.as_ref()) != obj_equality_key(third)
            {
                return Err("union De Morgan changed its repeated operands".into());
            }
            (first, second, third, "setMinusUnionDeMorgan")
        }
        _ => return Err("non-three-set rule reached structural renderer".into()),
    };
    Ok(format!(
        "Litex.SetRules.{theorem} {} {} {}",
        render_obj(first, context)?,
        render_obj(second, context)?,
        render_obj(third, context)?
    ))
}

fn render_structural_set_equality(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanSetBuiltinRuleIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right) = equality_parts(&fact.proposition)?;
    render_fact(&fact.proposition, context)?;
    let symmetric = |proof: String| format!("Litex.Same.symm ({proof})");
    match rule {
        LitexToLeanSetBuiltinRuleIr::UnionCommutative => {
            let (Obj::Union(left_union), Obj::Union(right_union)) = (left, right) else {
                return Err("union commutativity changed its constructors".into());
            };
            if obj_equality_key(left_union.left.as_ref())
                != obj_equality_key(right_union.right.as_ref())
                || obj_equality_key(left_union.right.as_ref())
                    != obj_equality_key(right_union.left.as_ref())
            {
                return Err("union commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.unionCommutative {} {}",
                render_obj(left_union.left.as_ref(), context)?,
                render_obj(left_union.right.as_ref(), context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::UnionAssociative => {
            if let (Obj::Union(left_outer), Obj::Union(right_outer)) = (left, right) {
                if let Obj::Union(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Union(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.unionAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed = LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Anonymous,
                proposition: EqualFact::new(
                    right.clone(),
                    left.clone(),
                    fact.proposition.line_file(),
                )
                .into(),
                proof: LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ObjectReflexivity,
                    parameter_requirements: Vec::new(),
                    premises: Vec::new(),
                },
            };
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        LitexToLeanSetBuiltinRuleIr::UnionIdempotent => {
            if let Obj::Union(union) = left {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(right)
                {
                    return Ok(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(right, context)?
                    ));
                }
            }
            if let Obj::Union(union) = right {
                if obj_equality_key(union.left.as_ref()) == obj_equality_key(union.right.as_ref())
                    && obj_equality_key(union.left.as_ref()) == obj_equality_key(left)
                {
                    return Ok(symmetric(format!(
                        "Litex.SetRules.unionIdempotent {}",
                        render_obj(left, context)?
                    )));
                }
            }
            Err("union idempotence changed its repeated operand".into())
        }
        LitexToLeanSetBuiltinRuleIr::UnionEmptyIdentity => {
            for (union_side, plain_side, reverse) in [(left, right, false), (right, left, true)] {
                let Obj::Union(union) = union_side else {
                    continue;
                };
                let left_empty =
                    matches!(union.left.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let right_empty =
                    matches!(union.right.as_ref(), Obj::ListSet(set) if set.list.is_empty());
                let operand = if left_empty {
                    union.right.as_ref()
                } else if right_empty {
                    union.left.as_ref()
                } else {
                    continue;
                };
                if obj_equality_key(operand) != obj_equality_key(plain_side) {
                    continue;
                }
                let theorem = if left_empty {
                    "unionEmptyLeft"
                } else {
                    "unionEmptyRight"
                };
                let proof = format!(
                    "Litex.SetRules.{theorem} {}",
                    render_obj(plain_side, context)?
                );
                return Ok(if reverse { symmetric(proof) } else { proof });
            }
            Err("union empty identity changed its empty or retained operand".into())
        }
        LitexToLeanSetBuiltinRuleIr::IntersectCommutative => {
            let (Obj::Intersect(left_intersection), Obj::Intersect(right_intersection)) =
                (left, right)
            else {
                return Err("intersection commutativity changed its constructors".into());
            };
            if obj_equality_key(left_intersection.left.as_ref())
                != obj_equality_key(right_intersection.right.as_ref())
                || obj_equality_key(left_intersection.right.as_ref())
                    != obj_equality_key(right_intersection.left.as_ref())
            {
                return Err("intersection commutativity changed its swapped operands".into());
            }
            Ok(format!(
                "Litex.SetRules.intersectCommutative {} {}",
                render_obj(left_intersection.left.as_ref(), context)?,
                render_obj(left_intersection.right.as_ref(), context)?
            ))
        }
        LitexToLeanSetBuiltinRuleIr::IntersectAssociative => {
            if let (Obj::Intersect(left_outer), Obj::Intersect(right_outer)) = (left, right) {
                if let Obj::Intersect(left_inner) = left_outer.left.as_ref() {
                    if obj_equality_key(left_inner.left.as_ref())
                        == obj_equality_key(right_outer.left.as_ref())
                    {
                        if let Obj::Intersect(right_inner) = right_outer.right.as_ref() {
                            if obj_equality_key(left_inner.right.as_ref())
                                == obj_equality_key(right_inner.left.as_ref())
                                && obj_equality_key(left_outer.right.as_ref())
                                    == obj_equality_key(right_inner.right.as_ref())
                            {
                                return Ok(format!(
                                    "Litex.SetRules.intersectAssociative {} {} {}",
                                    render_obj(left_inner.left.as_ref(), context)?,
                                    render_obj(left_inner.right.as_ref(), context)?,
                                    render_obj(left_outer.right.as_ref(), context)?
                                ));
                            }
                        }
                    }
                }
            }
            let reversed = LitexToLeanFactIr {
                storage: LitexToLeanFactStorageIr::Anonymous,
                proposition: EqualFact::new(
                    right.clone(),
                    left.clone(),
                    fact.proposition.line_file(),
                )
                .into(),
                proof: LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::ObjectReflexivity,
                    parameter_requirements: Vec::new(),
                    premises: Vec::new(),
                },
            };
            Ok(symmetric(render_structural_set_equality(
                &reversed, rule, context,
            )?))
        }
        _ => Err("non-equality set rule reached structural equality renderer".into()),
    }
}

fn render_list_set_membership(
    fact: &LitexToLeanFactIr,
    selected_index: usize,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "list-set membership requires one selected equality and no parameter requirements"
                .into(),
        );
    }
    let (element, set) = membership_parts(&fact.proposition)?;
    let Obj::ListSet(list_set) = set else {
        return Err("list-set membership certificate targets another set constructor".into());
    };
    let selected = list_set
        .list
        .get(selected_index)
        .ok_or_else(|| "list-set membership certificate has an out-of-range index".to_string())?;
    let (equality_left, equality_right) = equality_parts(&premises[0].proposition)?;
    if obj_equality_key(equality_left) != obj_equality_key(element)
        || obj_equality_key(equality_right) != obj_equality_key(selected.as_ref())
    {
        return Err("list-set membership equality changed its selected source element".into());
    }
    let selected_term = render_obj(selected.as_ref(), context)?;
    let equality = render_proof(&premises[0], context)?;
    let (witness, representation) =
        render_list_set_representation_bridge(&selected_term, selected_index);
    render_obj(set, context)?;
    Ok(format!(
        "⟨{witness}, Litex.Same.trans ({equality}) ({representation})⟩"
    ))
}

fn render_list_set_membership_elimination(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "list-set membership elimination requires one membership and no parameter requirements"
                .into(),
        );
    }
    let (element, set) = membership_parts(&premises[0].proposition)?;
    let Obj::ListSet(list_set) = set else {
        return Err("list-set membership elimination cites another set constructor".into());
    };
    if list_set.list.is_empty() {
        return Err("empty list-set membership cannot produce an equality branch".into());
    }
    let target_components = if list_set.list.len() == 1 {
        vec![fact.proposition.clone()]
    } else {
        disjunction_components(&fact.proposition)?
    };
    if target_components.len() != list_set.list.len() {
        return Err("list-set membership inference changed its branch count".into());
    }
    for (component, item) in target_components.iter().zip(list_set.list.iter()) {
        let (left, right) = equality_parts(component)?;
        if obj_equality_key(left) != obj_equality_key(element)
            || obj_equality_key(right) != obj_equality_key(item.as_ref())
        {
            return Err(
                "list-set membership inference changed its ordered equality branches".into(),
            );
        }
    }
    render_fact(&fact.proposition, context)?;
    let source = render_proof(&premises[0], context)?;
    let item_terms = list_set
        .list
        .iter()
        .map(|item| render_obj(item.as_ref(), context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut lines = vec![
        "(by".to_string(),
        format!("  rcases ({source}) with ⟨__member, __same⟩"),
    ];
    render_list_set_elimination_cases(&item_terms, 0, "__member", "  ", &mut lines);
    lines.push(")".into());
    Ok(lines.join("\n"))
}

fn render_list_set_elimination_cases(
    item_terms: &[String],
    index: usize,
    member: &str,
    indent: &str,
    lines: &mut Vec<String>,
) {
    let head = format!("__head{index}");
    let tail = format!("__tail{index}");
    lines.push(format!("{indent}cases {member} with"));
    lines.push(format!("{indent}| inl {head} =>"));
    lines.push(format!("{indent}  cases {head}"));
    let (_, representation) = render_list_set_representation_bridge(&item_terms[index], index);
    let equality = format!("Litex.Same.trans __same (Litex.Same.symm ({representation}))");
    lines.push(format!(
        "{indent}  exact {}",
        inject_disjunction_branch(equality, index, item_terms.len())
    ));
    lines.push(format!("{indent}| inr {tail} =>"));
    if index + 1 == item_terms.len() {
        lines.push(format!("{indent}  exact PEmpty.elim {tail}"));
    } else {
        render_list_set_elimination_cases(
            item_terms,
            index + 1,
            &tail,
            &format!("{indent}  "),
            lines,
        );
    }
}

fn inject_disjunction_branch(
    mut proof: String,
    selected_index: usize,
    branch_count: usize,
) -> String {
    if branch_count == 1 {
        return proof;
    }
    if selected_index + 1 < branch_count {
        proof = format!("Or.inl ({proof})");
    }
    for _ in 0..selected_index {
        proof = format!("Or.inr ({proof})");
    }
    proof
}

fn render_list_set_representation_bridge(
    selected_term: &str,
    selected_index: usize,
) -> (String, String) {
    let mut witness = "Litex.SingletonCarrier.element".to_string();
    let mut representation = format!("Litex.Same.singleton {selected_term}");
    representation =
        format!("Litex.Same.trans ({representation}) (Litex.Same.sumLeft ({witness}))");
    witness = format!("Sum.inl ({witness})");
    for _ in 0..selected_index {
        representation =
            format!("Litex.Same.trans ({representation}) (Litex.Same.sumRight ({witness}))");
        witness = format!("Sum.inr ({witness})");
    }
    (witness, representation)
}

fn render_tuple_literal_shape(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("tuple-literal shape reflection requires no retained premises".into());
    }
    let Fact::AtomicFact(AtomicFact::IsTupleFact(target)) = &fact.proposition else {
        return Err("tuple-literal shape evidence retained a non-tuple target".into());
    };
    let Obj::Tuple(tuple) = &target.set else {
        return Err("tuple-literal shape evidence changed its exact object".into());
    };
    if tuple.args.len() < 2 {
        return Err("tuple-literal shape evidence retained fewer than two items".into());
    }
    render_fact(&fact.proposition, context)?;
    Ok("⟨inferInstance⟩".into())
}

fn render_nonzero_numeric_membership(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 2 {
        return Err(
            "nonzero numeric membership requires two premises and no parameter requirements".into(),
        );
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    let (base_element, base_set) = membership_parts(&premises[0].proposition)?;
    let (nonzero_left, nonzero_right) = not_equal_parts(&premises[1].proposition)?;
    if obj_equality_key(target_element) != obj_equality_key(base_element)
        || obj_equality_key(target_element) != obj_equality_key(nonzero_left)
        || !matches!(nonzero_right, Obj::Number(number) if number.normalized_value == "0")
    {
        return Err("nonzero numeric membership changed its retained source element".into());
    }
    let theorem = match (target_set, base_set) {
        (Obj::StandardSet(StandardSet::ZStar), Obj::StandardSet(StandardSet::Z)) => {
            "inZStarOfInZNotSameZero"
        }
        (Obj::StandardSet(StandardSet::QStar), Obj::StandardSet(StandardSet::Q)) => {
            "inQStarOfInQNotSameZero"
        }
        (Obj::StandardSet(StandardSet::RStar), Obj::StandardSet(StandardSet::R)) => {
            "inRStarOfInRNotSameZero"
        }
        (Obj::StandardSet(StandardSet::CStar), Obj::StandardSet(StandardSet::C)) => {
            "inCStarOfInCNotSameZero"
        }
        _ => {
            return Err(
                "nonzero numeric membership changed its exact base or refined carrier".into(),
            );
        }
    };
    Ok(format!(
        "Litex.Rules.{theorem} ({}) ({})",
        render_proof(&premises[0], context)?,
        render_proof(&premises[1], context)?
    ))
}

fn render_nonzero_numeric_membership_elimination(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "nonzero numeric membership elimination requires one premise and no parameter requirements"
                .into(),
        );
    }
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    let (target_left, target_right) = not_equal_parts(&fact.proposition)?;
    if obj_equality_key(source_element) != obj_equality_key(target_left)
        || !matches!(target_right, Obj::Number(number) if number.normalized_value == "0")
    {
        return Err(
            "nonzero numeric membership elimination changed its retained source element or zero orientation"
                .into(),
        );
    }
    let theorem = match source_set {
        Obj::StandardSet(StandardSet::ZStar) => "notSameZeroOfInZStar",
        Obj::StandardSet(StandardSet::QStar) => "notSameZeroOfInQStar",
        Obj::StandardSet(StandardSet::RStar) => "notSameZeroOfInRStar",
        Obj::StandardSet(StandardSet::CStar) => "notSameZeroOfInCStar",
        _ => {
            return Err(
                "nonzero numeric membership elimination retained a non-star source carrier".into(),
            );
        }
    };
    Ok(format!(
        "Litex.Rules.{theorem} ({})",
        render_proof(&premises[0], context)?
    ))
}

fn render_native_constant_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanNativeConstantMembershipBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("native constant membership retained unexpected premises".into());
    }
    let (element, set) = membership_parts(&fact.proposition)?;
    let theorem = match (rule, element, set) {
        (
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::ImaginaryUnitInComplex,
            Obj::ImaginaryUnit(_),
            Obj::StandardSet(StandardSet::C),
        ) => "imaginaryUnitInC",
        (
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::EulerNumberInReal,
            Obj::EulerNumber(_),
            Obj::StandardSet(StandardSet::R),
        ) => "eInR",
        (
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::PiInReal,
            Obj::Pi(_),
            Obj::StandardSet(StandardSet::R),
        ) => "piInR",
        (
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::EulerNumberInPositiveReal,
            Obj::EulerNumber(_),
            Obj::StandardSet(StandardSet::RPos),
        ) => "eInRPos",
        (
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::PiInPositiveReal,
            Obj::Pi(_),
            Obj::StandardSet(StandardSet::RPos),
        ) => "piInRPos",
        _ => return Err("native constant membership changed its constant or carrier".into()),
    };
    Ok(format!("Litex.Rules.{theorem}"))
}

fn render_positive_real_membership(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "positive-real membership elimination requires one premise and no parameter requirements"
                .into(),
        );
    }
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    if !matches!(source_set, Obj::StandardSet(StandardSet::RPos)) {
        return Err("positive-real membership retained a source carrier other than R+".into());
    }
    let target_element = match &fact.proposition {
        Fact::AtomicFact(AtomicFact::LessFact(order)) if order.left.to_string() == "0" => {
            &order.right
        }
        Fact::AtomicFact(AtomicFact::GreaterFact(order)) if order.right.to_string() == "0" => {
            &order.left
        }
        _ => {
            return Err(
                "positive-real membership targets a fact other than strict positivity".into(),
            );
        }
    };
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("positive-real membership changed its inferred object".into());
    }
    Ok(format!(
        "Litex.Rules.positiveOfInRPos ({})",
        render_proof(&premises[0], context)?
    ))
}

fn render_natural_membership_implies_nonnegative(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "natural-membership nonnegativity requires one premise and no parameter requirements"
                .into(),
        );
    }
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    if !matches!(source_set, Obj::StandardSet(StandardSet::N)) {
        return Err(
            "natural-membership nonnegativity retained a source carrier other than N".into(),
        );
    }
    let target_element = match &fact.proposition {
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(order))
            if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") =>
        {
            &order.left
        }
        Fact::AtomicFact(AtomicFact::LessEqualFact(order))
            if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") =>
        {
            &order.right
        }
        _ => {
            return Err(
                "natural-membership nonnegativity targets a fact other than the source object being at least zero"
                    .into(),
            )
        }
    };
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("natural-membership nonnegativity changed its inferred object".into());
    }
    Ok(format!(
        "Litex.Rules.nonnegativeOfInN ({})",
        render_proof(&premises[0], context)?
    ))
}

fn render_complex_binary_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || !premises.is_empty() {
        return Err("complex binary membership closure retained unexpected proof premises".into());
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    if !matches!(target_set, Obj::StandardSet(StandardSet::C)) {
        return Err("complex binary membership target is not C".into());
    }
    let (left, right, theorem) = match (rule, target_element) {
        (LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Add, Obj::Add(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInC",
        ),
        (LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInC",
        ),
        (LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInC",
        ),
        (LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Div, Obj::Div(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInC",
        ),
        _ => return Err("complex binary membership target changed its operator".into()),
    };
    Ok(format!(
        "Litex.Rules.{theorem} {} {}",
        render_obj(left, context)?,
        render_obj(right, context)?
    ))
}

fn render_integer_binary_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanIntegerMembershipClosureBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "integer binary membership closure requires one ordered conjunction and no parameter requirements"
                .into(),
        );
    }
    let components = conjunction_components(&premises[0].proposition)?;
    if components.len() != 2 {
        return Err("integer binary membership premise is not a binary conjunction".into());
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    if !matches!(target_set, Obj::StandardSet(StandardSet::Z)) {
        return Err("integer binary membership target is not Z".into());
    }
    let (left, right, theorem) = match (rule, target_element) {
        (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Add, Obj::Add(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInZ",
        ),
        (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInZ",
        ),
        (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInZ",
        ),
        _ => {
            return Err(format!(
                "unsupported integer membership closure rule: {rule:?}"
            ));
        }
    };
    let (premise_left, premise_left_set) = membership_parts(&components[0])?;
    let (premise_right, premise_right_set) = membership_parts(&components[1])?;
    if !matches!(premise_left_set, Obj::StandardSet(StandardSet::Z))
        || !matches!(premise_right_set, Obj::StandardSet(StandardSet::Z))
        || obj_equality_key(left) != obj_equality_key(premise_left)
        || obj_equality_key(right) != obj_equality_key(premise_right)
    {
        return Err("integer binary membership premises changed its ordered operands".into());
    }
    let uses_local_numeric_view = [left, right].iter().any(|object| {
        matches!(object, Obj::Atom(atom) if atom
            .symbol_ref()
            .is_some_and(|symbol| context
                .numeric_representation_memberships
                .contains_key(&symbol.id())))
    });
    if !uses_local_numeric_view {
        let pair = render_proof(&premises[0], context)?;
        let pair_type = render_fact(&premises[0].proposition, context)?;
        return Ok(format!(
            "(by\n  have __components : {pair_type} := {pair}\n  exact Litex.Rules.{theorem} (__components.1) (__components.2))"
        ));
    }
    let LitexToLeanFactProofIr::RuleApplication {
        rule: LitexToLeanProofRuleIr::AndIntroduction,
        parameter_requirements: conjunction_parameters,
        premises: conjunction_premises,
    } = &premises[0].proof
    else {
        return Err("integer binary membership conjunction lost its introduction proof".into());
    };
    if !conjunction_parameters.is_empty() || conjunction_premises.len() != 2 {
        return Err("integer binary membership conjunction changed its proof components".into());
    }
    let left_fallback = render_proof(&conjunction_premises[0], context)?;
    let right_fallback = render_proof(&conjunction_premises[1], context)?;
    let left_proof = render_numeric_operand_membership(left, &left_fallback, context);
    let right_proof = render_numeric_operand_membership(right, &right_fallback, context);
    Ok(format!(
        "Litex.Rules.{theorem} ({left_proof}) ({right_proof})"
    ))
}

fn render_numeric_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    let proof = match object {
        Obj::Atom(atom) => atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_representation_memberships.get(&symbol.id())),
        _ => None,
    };
    proof.map_or_else(|| fallback.to_string(), Clone::clone)
}

fn render_natural_binary_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanNaturalMembershipClosureBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 2 {
        return Err(
            "natural binary membership closure requires two ordered premises and no parameter requirements"
                .into(),
        );
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    if !matches!(target_set, Obj::StandardSet(StandardSet::N)) {
        return Err("natural binary membership target is not N".into());
    }
    let (left, right, theorem) = match (rule, target_element) {
        (LitexToLeanNaturalMembershipClosureBuiltinRuleIr::Add, Obj::Add(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInN",
        ),
        (LitexToLeanNaturalMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInN",
        ),
        _ => return Err("natural binary membership target changed its operator".into()),
    };
    let (premise_left, premise_left_set) = membership_parts(&premises[0].proposition)?;
    let (premise_right, premise_right_set) = membership_parts(&premises[1].proposition)?;
    if !matches!(premise_left_set, Obj::StandardSet(StandardSet::N))
        || !matches!(premise_right_set, Obj::StandardSet(StandardSet::N))
        || obj_equality_key(left) != obj_equality_key(premise_left)
        || obj_equality_key(right) != obj_equality_key(premise_right)
    {
        return Err("natural binary membership premises changed its ordered operands".into());
    }
    let left_proof = render_proof(&premises[0], context)?;
    let right_proof = render_proof(&premises[1], context)?;
    Ok(format!(
        "Litex.Rules.{theorem} ({left_proof}) ({right_proof})"
    ))
}

fn render_rational_binary_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanRationalMembershipClosureBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "rational binary membership closure requires one ordered conjunction and no parameter requirements"
                .into(),
        );
    }
    let components = conjunction_components(&premises[0].proposition)?;
    if components.len() != 2 {
        return Err("rational binary membership premise is not a binary conjunction".into());
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    if !matches!(target_set, Obj::StandardSet(StandardSet::Q)) {
        return Err("rational binary membership target is not Q".into());
    }
    let (left, right, theorem) = match (rule, target_element) {
        (LitexToLeanRationalMembershipClosureBuiltinRuleIr::Add, Obj::Add(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInQ",
        ),
        (LitexToLeanRationalMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInQ",
        ),
        (LitexToLeanRationalMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInQ",
        ),
        (LitexToLeanRationalMembershipClosureBuiltinRuleIr::Div, Obj::Div(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInQ",
        ),
        _ => {
            return Err(format!(
                "unsupported rational membership closure rule: {rule:?}"
            ));
        }
    };
    let (premise_left, premise_left_set) = membership_parts(&components[0])?;
    let (premise_right, premise_right_set) = membership_parts(&components[1])?;
    if !matches!(premise_left_set, Obj::StandardSet(StandardSet::Q))
        || !matches!(premise_right_set, Obj::StandardSet(StandardSet::Q))
        || obj_equality_key(left) != obj_equality_key(premise_left)
        || obj_equality_key(right) != obj_equality_key(premise_right)
    {
        return Err("rational binary membership premises changed its ordered operands".into());
    }
    let pair = render_proof(&premises[0], context)?;
    let pair_type = render_fact(&premises[0].proposition, context)?;
    Ok(format!(
        "(by\n  have __components : {pair_type} := {pair}\n  exact Litex.Rules.{theorem} (__components.1) (__components.2))"
    ))
}

fn render_additive_sign_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanArithmeticBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 2 {
        return Err(
            "additive sign rule requires two premises and no parameter requirements".into(),
        );
    }
    let (target_is_strict, left_is_strict, right_is_strict, theorem) = match rule {
        LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative => {
            (false, false, false, "complexAddNonnegative")
        }
        LitexToLeanArithmeticBuiltinRuleIr::AddPositive => (true, true, true, "complexAddPositive"),
        LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict => {
            (true, true, false, "complexAddPositiveLeftStrict")
        }
        LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict => {
            (true, false, true, "complexAddPositiveRightStrict")
        }
        LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative => {
            (false, false, false, "complexMulNonnegative")
        }
        LitexToLeanArithmeticBuiltinRuleIr::MulPositive => (true, true, true, "complexMulPositive"),
        LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative => {
            (false, false, true, "complexDivNonnegative")
        }
        LitexToLeanArithmeticBuiltinRuleIr::DivPositive => (true, true, true, "complexDivPositive"),
        _ => return Err(format!("unsupported sign builtin rule: {rule:?}")),
    };

    let (target_zero, target_expression) =
        positive_order_parts(&fact.proposition, target_is_strict)?;
    let (target_left, target_right) = match (rule, target_expression) {
        (
            LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative
            | LitexToLeanArithmeticBuiltinRuleIr::AddPositive
            | LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict
            | LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict,
            Obj::Add(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative
            | LitexToLeanArithmeticBuiltinRuleIr::MulPositive,
            Obj::Mul(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative
            | LitexToLeanArithmeticBuiltinRuleIr::DivPositive,
            Obj::Div(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        _ => {
            return Err(format!(
                "sign builtin rule {rule:?} changed its target operator"
            ));
        }
    };
    let (left_zero, left_operand) = positive_order_parts(&premises[0].proposition, left_is_strict)?;
    let (right_zero, right_operand) =
        positive_order_parts(&premises[1].proposition, right_is_strict)?;
    if target_zero.to_string() != "0"
        || left_zero.to_string() != "0"
        || right_zero.to_string() != "0"
    {
        return Err("sign builtin rule changed its zero endpoint".into());
    }
    if obj_equality_key(target_left) != obj_equality_key(left_operand)
        || obj_equality_key(target_right) != obj_equality_key(right_operand)
    {
        return Err("sign builtin rule premises do not match its ordered operands".into());
    }

    let left = render_proof(&premises[0], context)?;
    let right = render_proof(&premises[1], context)?;
    Ok(format!("Litex.Rules.{theorem} ({left}) ({right})"))
}

fn render_order_transitivity(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() < 3 {
        return Err(
            "order transitivity requires carrier evidence followed by two ordered premises".into(),
        );
    }
    let (carrier_evidence, ordered_premises) = premises.split_at(premises.len() - 2);
    let [first, second] = ordered_premises else {
        unreachable!("split retained exactly two ordered premises")
    };
    for evidence in carrier_evidence {
        let components = match &evidence.proposition {
            Fact::AndFact(_) | Fact::ChainFact(_) => conjunction_components(&evidence.proposition)?,
            _ => vec![evidence.proposition.clone()],
        };
        for component in components {
            let (_object, set) = membership_parts(&component)?;
            if !matches!(set, Obj::StandardSet(StandardSet::R | StandardSet::Z)) {
                return Err(
                    "order transitivity carrier evidence changed from the verified R/Z fragment"
                        .into(),
                );
            }
        }
        render_proof(evidence, context)?;
    }

    let (target_left, target_right, target_strict) = order_relation_parts(&fact.proposition)?;
    let (first_left, middle, first_strict) = order_relation_parts(&first.proposition)?;
    let (second_left, second_right, second_strict) = order_relation_parts(&second.proposition)?;
    if obj_equality_key(target_left) != obj_equality_key(first_left)
        || obj_equality_key(middle) != obj_equality_key(second_left)
        || obj_equality_key(target_right) != obj_equality_key(second_right)
        || (target_strict && !first_strict && !second_strict)
    {
        return Err("order transitivity changed its endpoints, middle term, or strictness".into());
    }

    // Zero-ended relations deliberately use Positive/Nonnegative and have a
    // different one-representative contract. Keep that mixed bridge closed
    // until the verifier exposes a dedicated certificate for it.
    if target_left.to_string() == "0"
        || first_left.to_string() == "0"
        || second_left.to_string() == "0"
    {
        return Err("mixed zero-ended order transitivity has no reviewed Lean adapter".into());
    }

    let first_proof = render_proof(first, context)?;
    let second_proof = render_proof(second, context)?;
    if target_strict {
        return Ok(match (first_strict, second_strict) {
            (true, true) => format!("Litex.Lt.trans ({first_proof}) ({second_proof})"),
            (true, false) => format!("Litex.Lt.transLe ({first_proof}) ({second_proof})"),
            (false, true) => format!("Litex.Le.transLt ({first_proof}) ({second_proof})"),
            (false, false) => unreachable!("strict target validation rejected two weak premises"),
        });
    }

    let first_le = if first_strict {
        format!("Litex.Lt.toLe ({first_proof})")
    } else {
        format!("({first_proof})")
    };
    let second_le = if second_strict {
        format!("Litex.Lt.toLe ({second_proof})")
    } else {
        format!("({second_proof})")
    };
    Ok(format!("Litex.Le.trans {first_le} {second_le}"))
}

fn render_real_binary_membership_rule(
    fact: &LitexToLeanFactIr,
    rule: LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "real binary membership requires one conjunction premise and no parameter requirements"
                .into(),
        );
    }
    let components = conjunction_components(&premises[0].proposition)?;
    if components.len() != 2 {
        return Err("real binary membership premise is not a binary conjunction".into());
    }
    let (target_element, target_set) = membership_parts(&fact.proposition)?;
    let (target_left, target_right, theorem) = match (rule, target_element) {
        (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add, Obj::Add(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInR",
        ),
        (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInR",
        ),
        (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInR",
        ),
        (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div, Obj::Div(operation)) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInR",
        ),
        _ => return Err("real binary membership target changed its operator".into()),
    };
    if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
        return Err("real binary membership target is not R".into());
    }
    let (left_element, left_set) = membership_parts(&components[0])?;
    let (right_element, right_set) = membership_parts(&components[1])?;
    if !matches!(left_set, Obj::StandardSet(StandardSet::R))
        || !matches!(right_set, Obj::StandardSet(StandardSet::R))
        || obj_equality_key(target_left) != obj_equality_key(left_element)
        || obj_equality_key(target_right) != obj_equality_key(right_element)
    {
        return Err("real binary membership premises changed its ordered operands".into());
    }
    let uses_local_numeric_view = [target_left, target_right].iter().any(|object| {
        matches!(object, Obj::Atom(atom) if atom
            .symbol_ref()
            .is_some_and(|symbol| context.numeric_real_values.contains_key(&symbol.id())))
    });
    if !uses_local_numeric_view {
        let pair = render_proof(&premises[0], context)?;
        let pair_type = render_fact(&premises[0].proposition, context)?;
        return Ok(format!(
            "(by\n  have __components : {pair_type} := {pair}\n  exact Litex.Rules.{theorem} (__components.1) (__components.2))"
        ));
    }
    let LitexToLeanFactProofIr::RuleApplication {
        rule: LitexToLeanProofRuleIr::AndIntroduction,
        parameter_requirements: conjunction_parameters,
        premises: conjunction_premises,
    } = &premises[0].proof
    else {
        return Err("real binary membership conjunction lost its introduction proof".into());
    };
    if !conjunction_parameters.is_empty() || conjunction_premises.len() != 2 {
        return Err("real binary membership conjunction changed its proof components".into());
    }
    let left_fallback = render_proof(&conjunction_premises[0], context)?;
    let right_fallback = render_proof(&conjunction_premises[1], context)?;
    let left_proof = render_real_operand_membership(target_left, &left_fallback, context);
    let right_proof = render_real_operand_membership(target_right, &right_fallback, context);
    Ok(format!(
        "Litex.Rules.{theorem} ({left_proof}) ({right_proof})"
    ))
}

fn render_real_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    let real = match object {
        Obj::Atom(atom) => atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_real_values.get(&symbol.id())),
        _ => None,
    };
    real.map_or_else(
        || fallback.to_string(),
        |real| format!("Litex.Rules.complexRealInR ({real})"),
    )
}

fn render_comparison_notation_duality(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty()
        || premises.len() != 1
        || !crate::litex_to_lean_ir::facts_are_comparison_notation_duals(
            &premises[0].proposition,
            &fact.proposition,
        )
        || render_fact(&premises[0].proposition, context)?
            != render_fact(&fact.proposition, context)?
    {
        return Err("comparison-notation duality changed its source or target".into());
    }
    render_proof(&premises[0], context)
}

fn render_known_equality_path(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.is_empty() {
        return Err("known-equality path has invalid premise arity".into());
    }
    let (target_left, target_right) = equality_parts(&fact.proposition)?;
    let mut current_key = obj_equality_key(target_left);
    let target_key = obj_equality_key(target_right);
    let mut accumulated = None;
    for premise in premises {
        if !matches!(
            premise.proof,
            LitexToLeanFactProofIr::KnownFactCitation { .. }
        ) {
            return Err("known-equality path lost an exact FactId citation".into());
        }
        let (premise_left, premise_right) = equality_parts(&premise.proposition)?;
        let left_key = obj_equality_key(premise_left);
        let right_key = obj_equality_key(premise_right);
        let (to_key, reverse) = if current_key == left_key {
            (right_key, false)
        } else if current_key == right_key {
            (left_key, true)
        } else {
            return Err("known-equality path contains disconnected steps".into());
        };
        let proof = render_proof(premise, context)?;
        let oriented = if reverse {
            format!("Litex.Same.symm ({proof})")
        } else {
            proof
        };
        accumulated = Some(match accumulated {
            None => oriented,
            Some(previous) => format!("Litex.Same.trans ({previous}) ({oriented})"),
        });
        current_key = to_key;
    }
    if current_key != target_key {
        return Err("known-equality path does not end at the target right-hand side".into());
    }
    accumulated.ok_or_else(|| "known-equality path retained no steps".into())
}

fn render_known_forall_instantiation(
    _fact: &LitexToLeanFactIr,
    source_fact_id: FactId,
    arguments: &[Obj],
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let theorem = context
        .fact_names
        .get(&source_fact_id)
        .ok_or_else(|| format!("known forall cites unavailable FactId `{source_fact_id}`"))?;
    let source = context
        .fact_propositions
        .get(&source_fact_id)
        .ok_or_else(|| format!("known forall FactId `{source_fact_id}` has no proposition"))?;
    let Fact::ForallFact(source) = source else {
        return Err(format!(
            "known forall FactId `{source_fact_id}` does not name a forall fact"
        ));
    };
    let source_parameters = source
        .params_def_with_type
        .collect_param_bindings_with_types();
    if source_parameters.len() != arguments.len()
        || arguments.len() != parameter_requirements.len()
        || source.dom_facts.len() != premises.len()
        || source.then_facts.len() != 1
    {
        return Err(
            "known forall changed its argument, requirement, domain, or result arity".into(),
        );
    }

    let mut terms = vec![theorem.clone()];
    for (((binding, source_type), argument), requirement) in source_parameters
        .iter()
        .zip(arguments.iter())
        .zip(parameter_requirements.iter())
    {
        let _ = binding;
        terms.push(render_obj(argument, context)?);
        match source_type {
            ParamType::Set(_) => {
                let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = &requirement.proposition
                else {
                    return Err("known forall set argument retained a non-set requirement".into());
                };
                if obj_equality_key(&sethood.set) != obj_equality_key(argument) {
                    return Err("known forall set requirement changed its argument".into());
                }
            }
            ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                validate_refined_set_argument_requirement(source_type, argument, requirement)?;
                terms.push(format!("({})", render_proof(requirement, context)?));
            }
            ParamType::Obj(_) => {
                terms.push(format!("({})", render_proof(requirement, context)?));
            }
        }
    }
    for premise in premises {
        terms.push(format!("({})", render_proof(premise, context)?));
    }
    Ok(format!("({})", terms.join(" ")))
}

fn render_and_introduction(
    fact: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() {
        return Err("conjunction introduction retained parameter requirements".into());
    }
    let components = conjunction_components(&fact.proposition)?;
    if components.len() != premises.len()
        || components
            .iter()
            .zip(premises.iter())
            .any(|(expected, actual)| expected.to_string() != actual.proposition.to_string())
    {
        return Err("conjunction introduction changed its ordered component proofs".into());
    }
    let proofs = premises
        .iter()
        .map(|premise| render_proof(premise, context))
        .collect::<Result<Vec<_>, _>>()?;
    right_associated_conjunction_proof(&proofs)
}

fn render_disjunction_introduction(
    fact: &LitexToLeanFactIr,
    selected_index: usize,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err(
            "disjunction introduction changed its target, selected proof, or premise arity".into(),
        );
    }
    let branches = disjunction_components(&fact.proposition)?;
    if branches.get(selected_index).map(ToString::to_string)
        != Some(premises[0].proposition.to_string())
    {
        return Err("disjunction introduction selected a different branch proposition".into());
    }
    right_associated_disjunction_injection(
        render_proof(&premises[0], context)?,
        selected_index,
        branches.len(),
    )
}

fn render_conjunction_projection(
    fact: &LitexToLeanFactIr,
    index: usize,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 1 {
        return Err("conjunction projection changed its source, target, or premise arity".into());
    }
    let components = conjunction_components(&premises[0].proposition)?;
    if components.get(index).map(ToString::to_string) != Some(fact.proposition.to_string()) {
        return Err("conjunction projection changed its retained component position".into());
    }
    let source = render_proof(&premises[0], context)?;
    conjunction_projection(&format!("({source})"), index, components.len())
}

fn construct_lean_proof_for_membership_equality_rewrite(
    target: &LitexToLeanFactIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !parameter_requirements.is_empty() || premises.len() != 2 {
        return Err("membership equality rewrite has unsupported certificate shape".into());
    }
    let (target_element, target_set) = membership_parts(&target.proposition)?;
    let (source_element, source_set) = membership_parts(&premises[0].proposition)?;
    if obj_equality_key(target_set) != obj_equality_key(source_set) {
        return Err("membership rewrite changed the set object".into());
    }
    let (left, right) = equality_parts(&premises[1].proposition)?;
    let source_key = obj_equality_key(source_element);
    let target_key = obj_equality_key(target_element);
    let left_key = obj_equality_key(left);
    let right_key = obj_equality_key(right);
    let direction = if source_key == left_key && target_key == right_key {
        "mp"
    } else if source_key == right_key && target_key == left_key {
        "mpr"
    } else {
        return Err("membership rewrite operands do not match equality evidence".into());
    };
    let membership = render_proof(&premises[0], context)?;
    let equality = render_proof(&premises[1], context)?;
    let set = render_obj(target_set, context)?;
    Ok(format!(
        "(Litex.In.congr {equality} {set}).{direction} {membership}"
    ))
}

fn construct_lean_proof_for_registered_rule(
    target: &LitexToLeanFactIr,
    rule: &crate::litex_to_lean_ir::LitexToLeanRegisteredRuleApplicationIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Some((set_rule, expected_bindings, expected_semantic_premises)) =
        registered_set_rule(rule)
    {
        if rule.bindings.len() != expected_bindings
            || parameter_requirements.len() != rule.bindings.len()
        {
            return Err(format!(
                "registered set rule `{}` changed its binding or requirement arity: expected {expected_bindings} bindings but retained {}/{}",
                rule.rule_id.as_str(),
                rule.bindings.len(),
                parameter_requirements.len()
            ));
        }
        if rule.bindings.iter().any(|binding| {
            !matches!(
                binding.param_type,
                LitexToLeanParameterTypeIr::Set | LitexToLeanParameterTypeIr::MemberOf { .. }
            )
        }) {
            return Err(format!(
                "registered set rule `{}` changed its parameter types",
                rule.rule_id.as_str()
            ));
        }
        let mut semantic_premises = Vec::new();
        for (binding, requirement) in rule.bindings.iter().zip(parameter_requirements.iter()) {
            match &binding.param_type {
                LitexToLeanParameterTypeIr::Set => {
                    let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = &requirement.proposition
                    else {
                        return Err("registered set parameter retained non-set evidence".into());
                    };
                    if LitexToLeanObjectIr::lower(&sethood.set)? != binding.object {
                        return Err(
                            "registered set parameter evidence changed its exact binding".into(),
                        );
                    }
                }
                LitexToLeanParameterTypeIr::MemberOf { set } => {
                    let (element, actual_set) = membership_parts(&requirement.proposition)?;
                    if LitexToLeanObjectIr::lower(element)? != binding.object
                        || LitexToLeanObjectIr::lower(actual_set)? != *set
                    {
                        return Err(
                            "registered member parameter evidence changed its exact binding".into(),
                        );
                    }
                    semantic_premises.push(requirement.clone());
                }
                _ => {
                    return Err(
                        "registered set rule retained a refined-set parameter unexpectedly".into(),
                    );
                }
            }
        }
        semantic_premises.extend_from_slice(premises);
        if semantic_premises.len() != expected_semantic_premises {
            return Err(format!(
                "registered set rule `{}` changed its semantic premise count",
                rule.rule_id.as_str()
            ));
        }
        return render_set_builtin_rule(target, set_rule, &[], &semantic_premises, context);
    }
    match rule.rule_id.as_str() {
        LESS_EQUAL_OF_LESS_RULE_ID
            if rule.semantic_fingerprint.as_hex() == LESS_EQUAL_OF_LESS_FINGERPRINT => {}
        ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID
            if rule.semantic_fingerprint.as_hex()
                == ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT =>
        {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict,
                &[],
                premises,
                context,
            );
        }
        ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID
            if rule.semantic_fingerprint.as_hex()
                == ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT =>
        {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict,
                &[],
                premises,
                context,
            );
        }
        ADD_NONNEGATIVE_RULE_ID
            if rule.semantic_fingerprint.as_hex() == ADD_NONNEGATIVE_FINGERPRINT =>
        {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative,
                &[],
                premises,
                context,
            );
        }
        ADD_POSITIVE_RULE_ID if rule.semantic_fingerprint.as_hex() == ADD_POSITIVE_FINGERPRINT => {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::AddPositive,
                &[],
                premises,
                context,
            );
        }
        MUL_NONNEGATIVE_RULE_ID
            if rule.semantic_fingerprint.as_hex() == MUL_NONNEGATIVE_FINGERPRINT =>
        {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative,
                &[],
                premises,
                context,
            );
        }
        MUL_POSITIVE_RULE_ID if rule.semantic_fingerprint.as_hex() == MUL_POSITIVE_FINGERPRINT => {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::MulPositive,
                &[],
                premises,
                context,
            );
        }
        DIV_NONNEGATIVE_RULE_ID
            if rule.semantic_fingerprint.as_hex() == DIV_NONNEGATIVE_FINGERPRINT =>
        {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative,
                &[],
                premises,
                context,
            );
        }
        DIV_POSITIVE_RULE_ID if rule.semantic_fingerprint.as_hex() == DIV_POSITIVE_FINGERPRINT => {
            validate_registered_binary_real_rule(rule, parameter_requirements, premises, context)?;
            return render_additive_sign_rule(
                target,
                LitexToLeanArithmeticBuiltinRuleIr::DivPositive,
                &[],
                premises,
                context,
            );
        }
        _ => {
            return Err(format!(
                "unsupported or changed registered rule certificate `{}`",
                rule.rule_id.as_str()
            ));
        }
    }
    if rule.bindings.len() != 2 || parameter_requirements.len() != 2 || premises.len() != 1 {
        return Err("less-to-less-equal registered rule changed its certificate shape".into());
    }
    for requirement in parameter_requirements {
        render_proof(requirement, context)?;
    }
    let (less_left, less_right) = less_parts(&premises[0].proposition)?;
    let (le_left, le_right) = less_equal_parts(&target.proposition)?;
    if obj_equality_key(less_left) != obj_equality_key(le_left)
        || obj_equality_key(less_right) != obj_equality_key(le_right)
    {
        return Err("less-to-less-equal rule changed its operands".into());
    }
    if less_left.to_string() == "0" {
        return Ok(format!(
            "Litex.Positive.toNonnegative {}",
            render_proof(&premises[0], context)?
        ));
    }
    Ok(format!(
        "Litex.Lt.toLe {}",
        render_proof(&premises[0], context)?
    ))
}

fn registered_set_rule(
    rule: &crate::litex_to_lean_ir::LitexToLeanRegisteredRuleApplicationIr,
) -> Option<(LitexToLeanSetBuiltinRuleIr, usize, usize)> {
    let fingerprint = rule.semantic_fingerprint.as_hex();
    Some(match rule.rule_id.as_str() {
        SET_EMPTY_SUBSET_RULE_ID if fingerprint == SET_EMPTY_SUBSET_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::EmptySubset, 1, 0)
        }
        SET_UNION_ASSOCIATIVE_RULE_ID if fingerprint == SET_UNION_ASSOCIATIVE_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionAssociative, 3, 0)
        }
        SET_UNION_COMMUTATIVE_RULE_ID if fingerprint == SET_UNION_COMMUTATIVE_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionCommutative, 2, 0)
        }
        SET_UNION_EMPTY_LEFT_RULE_ID if fingerprint == SET_UNION_EMPTY_LEFT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionEmptyIdentity, 1, 0)
        }
        SET_UNION_EMPTY_RIGHT_RULE_ID if fingerprint == SET_UNION_EMPTY_RIGHT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionEmptyIdentity, 1, 0)
        }
        SET_UNION_IDEMPOTENT_RULE_ID if fingerprint == SET_UNION_IDEMPOTENT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionIdempotent, 1, 0)
        }
        SET_UNION_MEMBERSHIP_LEFT_RULE_ID
            if fingerprint == SET_UNION_MEMBERSHIP_LEFT_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::UnionMembershipLeft, 3, 1)
        }
        SET_UNION_MEMBERSHIP_RIGHT_RULE_ID
            if fingerprint == SET_UNION_MEMBERSHIP_RIGHT_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::UnionMembershipRight, 3, 1)
        }
        SET_INTERSECT_ASSOCIATIVE_RULE_ID
            if fingerprint == SET_INTERSECT_ASSOCIATIVE_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectAssociative, 3, 0)
        }
        SET_INTERSECT_COMMUTATIVE_RULE_ID
            if fingerprint == SET_INTERSECT_COMMUTATIVE_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectCommutative, 2, 0)
        }
        SET_INTERSECT_MEMBERSHIP_RULE_ID if fingerprint == SET_INTERSECT_MEMBERSHIP_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::IntersectMembershipBoth, 3, 2)
        }
        SET_MINUS_MEMBERSHIP_RULE_ID if fingerprint == SET_MINUS_MEMBERSHIP_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SetMinusMembership, 3, 2)
        }
        SET_INTERSECT_EQ_LEFT_OF_SUBSET_RULE_ID
            if fingerprint == SET_INTERSECT_EQ_LEFT_OF_SUBSET_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectEqLeftOfSubset, 2, 1)
        }
        SET_INTERSECT_EQ_RIGHT_OF_SUBSET_RULE_ID
            if fingerprint == SET_INTERSECT_EQ_RIGHT_OF_SUBSET_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectEqRightOfSubset, 2, 1)
        }
        SET_INTERSECT_FINITE_RULE_ID if fingerprint == SET_INTERSECT_FINITE_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::IntersectFinite, 2, 2)
        }
        SET_INTERSECT_SUBSET_LEFT_RULE_ID
            if fingerprint == SET_INTERSECT_SUBSET_LEFT_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectSubsetLeft, 2, 0)
        }
        SET_INTERSECT_SUBSET_RIGHT_RULE_ID
            if fingerprint == SET_INTERSECT_SUBSET_RIGHT_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::IntersectSubsetRight, 2, 0)
        }
        SET_INTERSECT_UNION_DISTRIBUTIVE_RULE_ID
            if fingerprint == SET_INTERSECT_UNION_DISTRIBUTIVE_FINGERPRINT =>
        {
            (
                LitexToLeanSetBuiltinRuleIr::IntersectUnionDistributive,
                3,
                0,
            )
        }
        SET_POWER_SET_FINITE_RULE_ID if fingerprint == SET_POWER_SET_FINITE_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::PowerSetFinite, 1, 1)
        }
        SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID
            if fingerprint == SET_POWER_SET_MEMBERSHIP_OF_SUBSET_FINGERPRINT =>
        {
            (
                LitexToLeanSetBuiltinRuleIr::PowerSetMembershipOfSubset,
                2,
                1,
            )
        }
        SET_POWER_SET_NONEMPTY_RULE_ID if fingerprint == SET_POWER_SET_NONEMPTY_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::PowerSetNonempty, 1, 0)
        }
        SET_MINUS_FINITE_LEFT_RULE_ID if fingerprint == SET_MINUS_FINITE_LEFT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SetMinusFiniteLeft, 2, 1)
        }
        SET_MINUS_INTERSECT_DE_MORGAN_RULE_ID
            if fingerprint == SET_MINUS_INTERSECT_DE_MORGAN_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::SetMinusIntersectDeMorgan, 3, 0)
        }
        SET_MINUS_RECOVER_SUBSET_RULE_ID if fingerprint == SET_MINUS_RECOVER_SUBSET_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SetMinusRecoverSubset, 2, 1)
        }
        SET_MINUS_SUBSET_LEFT_RULE_ID if fingerprint == SET_MINUS_SUBSET_LEFT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SetMinusSubsetLeft, 2, 0)
        }
        SET_MINUS_UNION_DE_MORGAN_RULE_ID
            if fingerprint == SET_MINUS_UNION_DE_MORGAN_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::SetMinusUnionDeMorgan, 3, 0)
        }
        SET_SUBSET_EQ_SET_MINUS_RECOVERY_RULE_ID
            if fingerprint == SET_SUBSET_EQ_SET_MINUS_RECOVERY_FINGERPRINT =>
        {
            (LitexToLeanSetBuiltinRuleIr::SubsetEqSetMinusRecovery, 2, 1)
        }
        SET_SUBSET_UNION_LEFT_RULE_ID if fingerprint == SET_SUBSET_UNION_LEFT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SubsetUnionLeft, 2, 0)
        }
        SET_SUBSET_UNION_RIGHT_RULE_ID if fingerprint == SET_SUBSET_UNION_RIGHT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::SubsetUnionRight, 2, 0)
        }
        SET_UNION_FINITE_RULE_ID if fingerprint == SET_UNION_FINITE_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionFinite, 2, 2)
        }
        SET_UNION_NONEMPTY_LEFT_RULE_ID if fingerprint == SET_UNION_NONEMPTY_LEFT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionNonemptyLeft, 2, 1)
        }
        SET_UNION_NONEMPTY_RIGHT_RULE_ID if fingerprint == SET_UNION_NONEMPTY_RIGHT_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionNonemptyRight, 2, 1)
        }
        SET_UNION_SUBSET_RULE_ID if fingerprint == SET_UNION_SUBSET_FINGERPRINT => {
            (LitexToLeanSetBuiltinRuleIr::UnionSubset, 3, 2)
        }
        _ => return None,
    })
}

fn validate_registered_binary_real_rule(
    rule: &crate::litex_to_lean_ir::LitexToLeanRegisteredRuleApplicationIr,
    parameter_requirements: &[LitexToLeanFactIr],
    premises: &[LitexToLeanFactIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if rule.bindings.len() != 2 || parameter_requirements.len() != 2 || premises.len() != 2 {
        return Err("binary real registered rule changed its certificate shape".into());
    }
    for (binding, requirement) in rule.bindings.iter().zip(parameter_requirements.iter()) {
        let LitexToLeanParameterTypeIr::MemberOf { set: binding_set } = &binding.param_type else {
            return Err("binary real registered rule retained a non-membership binder".into());
        };
        if *binding_set != LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) {
            return Err("binary real registered rule changed a binder carrier".into());
        }
        let (element, set) = membership_parts(&requirement.proposition)?;
        if LitexToLeanObjectIr::lower(element)? != binding.object
            || LitexToLeanObjectIr::lower(set)?
                != LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
        {
            return Err("binary real registered rule changed its parameter evidence".into());
        }
        render_proof(requirement, context)?;
    }
    Ok(())
}

fn render_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match fact {
        Fact::AtomicFact(atomic) => match atomic {
            AtomicFact::NormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .map(|argument| render_obj(argument, context))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("{} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::NotNormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "¬ Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "¬ Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .map(|argument| render_obj(argument, context))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("¬ {} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::NotInFact(fact) => Ok(format!(
                "¬ Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::SupersetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::NotSubsetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::NotSupersetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::EqualFact(fact) => Ok(format!(
                "Litex.Same {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "¬ Litex.Same {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::LessFact(fact) => render_order_fact(&fact.left, &fact.right, true, context),
            AtomicFact::GreaterFact(fact) => {
                render_order_fact(&fact.right, &fact.left, true, context)
            }
            AtomicFact::LessEqualFact(fact) => {
                render_order_fact(&fact.left, &fact.right, false, context)
            }
            AtomicFact::GreaterEqualFact(fact) => {
                render_order_fact(&fact.right, &fact.left, false, context)
            }
            AtomicFact::NotLessFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, true, context)?
            )),
            AtomicFact::NotGreaterFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, true, context)?
            )),
            AtomicFact::NotLessEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, false, context)?
            )),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, false, context)?
            )),
            AtomicFact::IsNonemptySetFact(fact) => Ok(format!(
                "Litex.Set.Nonempty {}",
                render_obj(&fact.set, context)?
            )),
            AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
                "Litex.Set.Finite {}",
                render_obj(&fact.set, context)?
            )),
            AtomicFact::IsTupleFact(fact) => {
                Ok(format!("Litex.IsTuple {}", render_obj(&fact.set, context)?))
            }
            _ => Err(format!("unsupported compiler atomic fact `{fact}`")),
        },
        Fact::AndFact(_) | Fact::ChainFact(_) => {
            let components = conjunction_components(fact)?;
            let rendered = components
                .iter()
                .map(|component| render_fact(component, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(conjunction(&rendered))
        }
        Fact::OrFact(_) => {
            let branches = disjunction_components(fact)?;
            let rendered = branches
                .iter()
                .map(|branch| render_fact(branch, context))
                .collect::<Result<Vec<_>, _>>()?;
            if rendered.is_empty() {
                return Err("compiler disjunction retained no branches".into());
            }
            Ok(rendered.join(" ∨ "))
        }
        Fact::ExistFact(existential) => render_existential_fact(existential, context),
        Fact::ForallFact(forall) => render_forall_fact_type(forall, context),
        _ => Err(format!("unsupported compiler fact `{fact}`")),
    }
}

fn render_order_fact(
    left: &Obj,
    right: &Obj,
    strict: bool,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if left.to_string() == "0" {
        let predicate = if strict {
            "Litex.Positive"
        } else {
            "Litex.Nonnegative"
        };
        return Ok(format!("{predicate} {}", render_obj(right, context)?));
    }
    let predicate = if strict { "Litex.Lt" } else { "Litex.Le" };
    Ok(format!(
        "{predicate} {} {}",
        render_numeric_obj(left, context)?,
        render_numeric_obj(right, context)?
    ))
}

fn render_numeric_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    // Bound identifiers are not all stored as the same `Atom` constructor.
    // Lowering supplies their canonical SymbolId, which is the identity used
    // by the compiler environment regardless of the source atom shape.
    if let Ok(LitexToLeanObjectIr::Symbol { symbol_id, .. }) = LitexToLeanObjectIr::lower(obj) {
        if let Some(representation) = context.numeric_representations.get(&symbol_id) {
            return Ok(representation.clone());
        }
    }
    if let Obj::Atom(atom) = obj {
        if let Some(representation) = atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_representations.get(&symbol.id()))
        {
            return Ok(representation.clone());
        }
    }
    match obj {
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Div(operation) => Ok(format!(
            "({} / {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        _ => render_obj(obj, context),
    }
}

fn render_existential_fact(
    existential: &ExistFactEnum,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let name = lean_identifier(group.params[0].name());
    render_existential_fact_with_names(existential, context, &name, &format!("__carrier_{name}"))
}

fn render_existential_fact_with_names(
    existential: &ExistFactEnum,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    witness_name: &str,
    carrier_name: &str,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let set = parameter_set(&group.param_type)?;
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(group.params[0].id(), witness_name.to_string());
    nested
        .existential_names
        .insert(group.params[0].name().to_string(), witness_name.to_string());
    let requirement = format!("Litex.In {witness_name} {}", render_obj(set, &nested)?);
    let body = render_fact(&existential.facts()[0].from_ref_to_cloned_fact(), &nested)?;
    let binders = match set {
        Obj::FnSet(_) => format!("({carrier_name} : Type 1) ({witness_name} : {carrier_name})"),
        set if set_requires_heterogeneous_carrier(set) => {
            format!("({carrier_name} : Type) ({witness_name} : {carrier_name})")
        }
        _ => format!("({witness_name} : ℂ)"),
    };
    Ok(format!("∃ {binders}, {requirement} ∧ {body}"))
}

fn one_witness_existential_group(
    existential: &ExistFactEnum,
) -> Result<&ParamGroupWithParamType, String> {
    if !existential.is_plain_exist()
        || existential.params_def_with_type().number_of_params() != 1
        || existential.facts().len() != 1
    {
        return Err(
            "compiler existential facts support one positive witness and one body fact".into(),
        );
    }
    let group = &existential.params_def_with_type().groups[0];
    if group.params.len() != 1 {
        return Err("compiler existential fact requires one singleton parameter group".into());
    }
    parameter_set(&group.param_type)?;
    Ok(group)
}

fn one_witness_existentials_are_alpha_equal(
    source: &Fact,
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    let (Fact::ExistFact(source), Fact::ExistFact(target)) = (source, target) else {
        return Ok(false);
    };
    Ok(
        render_existential_fact_with_names(source, context, "__bound", "__bound_carrier")?
            == render_existential_fact_with_names(target, context, "__bound", "__bound_carrier")?,
    )
}

fn render_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match obj {
        Obj::Atom(AtomObj::Forall(parameter)) => context
            .symbol_names
            .get(&parameter.symbol.id())
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(AtomObj::Def(parameter)) => context
            .symbol_names
            .get(&parameter.symbol.id())
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(AtomObj::Exist(parameter)) => context
            .symbol_names
            .get(&parameter.symbol.id())
            .cloned()
            .or_else(|| context.existential_names.get(parameter.name()).cloned())
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(AtomObj::Identifier(identifier)) => identifier
            .symbol
            .as_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(atom) => atom
            .symbol_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Number(number)
            if !number.normalized_value.is_empty()
                && number
                    .normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("({} : ℂ)", number.normalized_value))
        }
        Obj::ImaginaryUnit(_) => Ok("Complex.I".into()),
        Obj::EulerNumber(_) => Ok("((Real.exp 1 : ℝ) : ℂ)".into()),
        Obj::Pi(_) => Ok("((Real.pi : ℝ) : ℂ)".into()),
        Obj::Add(addition) => Ok(format!(
            "({} + {})",
            render_numeric_obj(addition.left.as_ref(), context)?,
            render_numeric_obj(addition.right.as_ref(), context)?
        )),
        Obj::Sub(subtraction) => Ok(format!(
            "({} - {})",
            render_numeric_obj(subtraction.left.as_ref(), context)?,
            render_numeric_obj(subtraction.right.as_ref(), context)?
        )),
        Obj::Mul(multiplication) => Ok(format!(
            "({} * {})",
            render_numeric_obj(multiplication.left.as_ref(), context)?,
            render_numeric_obj(multiplication.right.as_ref(), context)?
        )),
        Obj::Div(division) => Ok(format!(
            "({} / {})",
            render_numeric_obj(division.left.as_ref(), context)?,
            render_numeric_obj(division.right.as_ref(), context)?
        )),
        Obj::FnSet(function_set) => {
            let function = LitexToLeanFunctionTypeIr::lower(function_set)?;
            render_function_set(&function, context)
        }
        Obj::SetBuilder(_) => {
            let lowered = LitexToLeanObjectIr::lower(obj)?;
            render_set_ir(&lowered, context)
        }
        Obj::AnonymousFn(_) => {
            let LitexToLeanObjectIr::AnonymousFunction(function) = LitexToLeanObjectIr::lower(obj)?
            else {
                return Err("anonymous function lowered to another object".into());
            };
            render_anonymous_function(&function, context)
        }
        Obj::FnObj(application) => {
            let LitexToLeanObjectIr::FunctionApplication(application) =
                LitexToLeanObjectIr::lower(&application.clone().into())?
            else {
                return Err("function application lowered to a non-application object".into());
            };
            render_function_application(&application, context)
        }
        Obj::StandardSet(set) => render_standard_set(*set).map(str::to_string),
        _ => render_object_ir(&LitexToLeanObjectIr::lower(obj)?, context),
    }
}

fn validate_set_parameter_premise(symbol_id: SymbolId, premise: &Fact) -> Result<(), String> {
    let Fact::AtomicFact(AtomicFact::IsSetFact(is_set)) = premise else {
        return Err(format!(
            "set parameter retained non-set evidence `{premise}`"
        ));
    };
    let Obj::Atom(atom) = &is_set.set else {
        return Err("set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

fn validate_object_parameter_premise(
    symbol_id: SymbolId,
    expected_set: &Obj,
    premise: &Fact,
) -> Result<(), String> {
    let (element, set) = membership_parts(premise)?;
    if !object_is_symbol(element, symbol_id) {
        return Err("object parameter evidence changed its SymbolId".into());
    }
    if obj_equality_key(set) != obj_equality_key(expected_set) {
        return Err("object parameter evidence changed its carrier set".into());
    }
    Ok(())
}

fn validate_refined_set_parameter_premise(
    symbol_id: SymbolId,
    param_type: &ParamType,
    premise: &Fact,
) -> Result<(), String> {
    let target = match (param_type, premise) {
        (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property))) => {
            &property.set
        }
        (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property))) => {
            &property.set
        }
        (ParamType::NonemptySet(_), _) => {
            return Err(format!(
                "nonempty-set parameter retained different evidence `{premise}`"
            ));
        }
        (ParamType::FiniteSet(_), _) => {
            return Err(format!(
                "finite-set parameter retained different evidence `{premise}`"
            ));
        }
        _ => return Err("refined-set validator received another parameter type".into()),
    };
    let Obj::Atom(atom) = target else {
        return Err("refined-set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("refined-set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

fn validate_refined_set_argument_requirement(
    param_type: &ParamType,
    argument: &Obj,
    requirement: &LitexToLeanFactIr,
) -> Result<(), String> {
    let target = match (param_type, &requirement.proposition) {
        (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property))) => {
            &property.set
        }
        (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property))) => {
            &property.set
        }
        (ParamType::NonemptySet(_), _) => {
            return Err("known forall nonempty-set argument retained different evidence".into());
        }
        (ParamType::FiniteSet(_), _) => {
            return Err("known forall finite-set argument retained different evidence".into());
        }
        _ => return Err("refined-set argument validator received another parameter type".into()),
    };
    if obj_equality_key(target) != obj_equality_key(argument) {
        return Err("known forall refined-set requirement changed its argument".into());
    }
    Ok(())
}

fn set_requires_heterogeneous_carrier(set: &Obj) -> bool {
    matches!(set, Obj::Atom(AtomObj::Forall(_)))
}

fn validate_unary_function_type(function: &LitexToLeanFunctionTypeIr) -> Result<(), String> {
    if function.parameters.len() != 1 {
        return Err("compiler function-set MVP supports exactly one parameter".into());
    }
    if let LitexToLeanObjectIr::FunctionSet { function } = function.return_set.as_ref() {
        validate_unary_function_type(function)?;
    }
    Ok(())
}

fn validate_function_type(function: &LitexToLeanFunctionTypeIr) -> Result<(), String> {
    if function.parameters.is_empty() {
        return Err("compiler function set retained an empty source parameter layer".into());
    }
    if let LitexToLeanObjectIr::FunctionSet { function } = function.return_set.as_ref() {
        validate_function_type(function)?;
    }
    Ok(())
}

fn function_uses_telescope(function: &LitexToLeanFunctionTypeIr) -> bool {
    if function.parameters.len() != 1 {
        return true;
    }
    if !function.domain_facts.is_empty()
        && matches!(
            function.parameters[0].set,
            LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural)
        )
    {
        // The finite-sequence bound depends on the natural representative
        // selected by the parameter's `N+` membership proof. A `FnWhere`
        // predicate receives only the heterogeneous value, while the
        // telescope parameter node owns both that value and its membership.
        return true;
    }
    let parameter_symbols = function
        .parameters
        .iter()
        .map(|parameter| parameter.symbol_id)
        .collect::<HashSet<_>>();
    function
        .parameters
        .iter()
        .any(|parameter| !object_ir_is_independent_of_symbols(&parameter.set, &parameter_symbols))
        || !object_ir_is_independent_of_symbols(function.return_set.as_ref(), &parameter_symbols)
}

fn object_ir_is_independent_of_symbols(
    object: &LitexToLeanObjectIr,
    symbol_ids: &HashSet<SymbolId>,
) -> bool {
    match object {
        LitexToLeanObjectIr::Symbol { symbol_id, .. } => !symbol_ids.contains(symbol_id),
        LitexToLeanObjectIr::FunctionSet { function } => {
            function
                .parameters
                .iter()
                .all(|parameter| object_ir_is_independent_of_symbols(&parameter.set, symbol_ids))
                && object_ir_is_independent_of_symbols(function.return_set.as_ref(), symbol_ids)
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            object_ir_is_independent_of_symbols(application.head.as_ref(), symbol_ids)
                && application.argument_layers.iter().all(|layer| {
                    layer
                        .iter()
                        .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids))
                })
        }
        LitexToLeanObjectIr::ClosedRange { start, end }
        | LitexToLeanObjectIr::Range { start, end } => {
            object_ir_is_independent_of_symbols(start, symbol_ids)
                && object_ir_is_independent_of_symbols(end, symbol_ids)
        }
        LitexToLeanObjectIr::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => {
            object_ir_is_independent_of_symbols(index_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_function, symbol_ids)
        }
        LitexToLeanObjectIr::SequenceSet { values, length } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && length
                    .as_ref()
                    .is_none_or(|length| object_ir_is_independent_of_symbols(length, symbol_ids))
        }
        LitexToLeanObjectIr::MatrixSet {
            values,
            row_count,
            column_count,
        } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && object_ir_is_independent_of_symbols(row_count, symbol_ids)
                && object_ir_is_independent_of_symbols(column_count, symbol_ids)
        }
        LitexToLeanObjectIr::Aggregate { arguments, .. } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        LitexToLeanObjectIr::TupleDimension(object) => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
        }
        LitexToLeanObjectIr::IndexedAccess { object, index } => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
                && object_ir_is_independent_of_symbols(index, symbol_ids)
        }
        LitexToLeanObjectIr::BuiltinApp { arguments, .. }
        | LitexToLeanObjectIr::Collection {
            items: arguments, ..
        } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        // Binder-owning objects are kept on the dependent telescope path. The
        // owned binder itself may hide a reference to an outer parameter in
        // one of its source facts, which the flattened IR does not erase.
        LitexToLeanObjectIr::SetBuilder(_) | LitexToLeanObjectIr::AnonymousFunction(_) => false,
        LitexToLeanObjectIr::Number { .. }
        | LitexToLeanObjectIr::Constant(_)
        | LitexToLeanObjectIr::StandardSet(_) => true,
    }
}

fn exact_set_real_value(set: &LitexToLeanObjectIr, value: &str) -> Option<String> {
    match set {
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℝ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) => {
            Some(format!("({value} : ℝ)"))
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            exact_set_real_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

fn exact_set_numeric_value(set: &LitexToLeanObjectIr, value: &str) -> Option<String> {
    match set {
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℂ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Natural) => {
            Some(format!("((({value} : ℕ)) : ℂ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Integer) => {
            Some(format!("((({value} : ℤ)) : ℂ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Rational) => {
            Some(format!("((({value} : ℚ)) : ℂ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) => {
            Some(format!("((({value} : ℝ)) : ℂ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Complex) => {
            Some(format!("({value} : ℂ)"))
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            exact_set_numeric_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

fn membership_real_value(
    set: &LitexToLeanObjectIr,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_real_value(set, &format!("Litex.In.rep {value} {membership}"))
}

fn membership_numeric_value(
    set: &LitexToLeanObjectIr,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_numeric_value(set, &format!("Litex.In.rep {value} {membership}"))
}

fn membership_numeric_proof(
    set: &LitexToLeanObjectIr,
    value: &str,
    membership: &str,
) -> Option<String> {
    let representative = format!("Litex.In.rep {value} {membership}");
    exact_set_numeric_proof(set, &representative)
}

fn exact_set_numeric_proof(set: &LitexToLeanObjectIr, value: &str) -> Option<String> {
    match set {
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural) => {
            Some(format!(
                "Litex.Rules.complexEqNatInNPos (((({value}).val : ℕ) : ℂ)) (({value}).val : ℕ) (by rfl) (({value}).property)"
            ))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Natural) => Some(format!(
            "Litex.Rules.complexEqNatInN ((({value} : ℕ) : ℂ)) ({value} : ℕ) (by rfl)"
        )),
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Integer) => Some(format!(
            "Litex.Rules.complexEqIntInZ ((({value} : ℤ) : ℂ)) ({value} : ℤ) (by rfl)"
        )),
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Rational) => Some(format!(
            "Litex.Rules.complexEqRatInQ ((({value} : ℚ) : ℂ)) ({value} : ℚ) (by rfl)"
        )),
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real) => {
            Some(format!("Litex.Rules.complexRealInR ({value} : ℝ)"))
        }
        LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Complex) => {
            Some(format!("Litex.Rules.complexInC ({value} : ℂ)"))
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            exact_set_numeric_proof(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

fn render_telescope_signature(
    function: &LitexToLeanFunctionTypeIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    validate_function_type(function)?;
    let mut nested = context.clone();
    let mut prefixes = Vec::with_capacity(function.parameters.len() + 1);
    for (index, parameter) in function.parameters.iter().enumerate() {
        let domain = render_set_ir(&parameter.set, &nested)?;
        let alpha = format!("__alpha{}", index + 1);
        let argument = format!("__arg{}", index + 1);
        let membership = format!("__arg{}_in", index + 1);
        prefixes.push(format!(
            "(Litex.FnTelescope.parameter {domain} (fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
        ));
        nested.symbol_names.insert(parameter.symbol_id, argument);
        if let Some(real) =
            membership_real_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) =
            membership_numeric_proof(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
    }
    if !function.domain_facts.is_empty() {
        let requirements = function
            .domain_facts
            .iter()
            .map(|fact| render_telescope_domain_requirement(function, fact, &nested))
            .collect::<Result<Vec<_>, _>>()?;
        prefixes.push(format!(
            "(Litex.FnTelescope.requirement ({}) (fun __domain => ",
            conjunction(&requirements)
        ));
    }
    let codomain = render_set_ir(function.return_set.as_ref(), &nested)?;
    let universe = if matches!(
        function.return_set.as_ref(),
        LitexToLeanObjectIr::FunctionSet { .. }
    ) {
        1
    } else {
        0
    };
    let signature = format!(
        "{}(Litex.FnTelescope.done {codomain}){}",
        prefixes.concat(),
        "))".repeat(prefixes.len())
    );
    Ok(format!("({signature} : Litex.FnTelescope.{{{universe}}})"))
}

/// A bounded `N+` source parameter is heterogeneous in Lean. Its source
/// domain fact still compares the original Litex argument, so the telescope
/// requirement retains that comparison through an existential complex
/// observation instead of silently comparing a chosen carrier value.
fn render_telescope_domain_requirement(
    function: &LitexToLeanFunctionTypeIr,
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Some((parameter_symbol_id, natural_bound)) =
        positive_natural_parameter_less_equal_natural_bound(function, fact)?
    {
        let parameter_name = context
            .symbol_names
            .get(&parameter_symbol_id)
            .ok_or_else(|| "bounded positive-natural parameter has no compiler name".to_string())?;
        return Ok(format!(
            "Litex.positiveNaturalParameterLessEqualNaturalBound {parameter_name} {natural_bound}"
        ));
    }
    render_fact(fact, context)
}

fn positive_natural_parameter_less_equal_natural_bound(
    function: &LitexToLeanFunctionTypeIr,
    fact: &Fact,
) -> Result<Option<(SymbolId, String)>, String> {
    let Fact::AtomicFact(AtomicFact::LessEqualFact(comparison)) = fact else {
        return Ok(None);
    };
    let Some(parameter) = function.parameters.iter().find(|parameter| {
        parameter.set == LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::PositiveNatural)
            && object_is_symbol(&comparison.left, parameter.symbol_id)
    }) else {
        return Ok(None);
    };
    let lowered_bound = LitexToLeanObjectIr::lower(&comparison.right)?;
    let natural_bound = render_natural_endpoint(&lowered_bound)?;
    Ok(Some((parameter.symbol_id, natural_bound)))
}

fn render_function_requirement(
    function: &LitexToLeanFunctionTypeIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function.domain_facts.is_empty() {
        return Err("total function has no source-domain requirement".into());
    }
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(function.parameters[0].symbol_id, "__arg".into());
    let requirements = function
        .domain_facts
        .iter()
        .map(|fact| render_fact(fact, &nested))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!(
        "(fun {{__alpha}} (__arg : __alpha) => {})",
        conjunction(&requirements)
    ))
}

fn render_function_type(
    function: &LitexToLeanFunctionTypeIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "Litex.FnTelescope.Carrier {}",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let domain = render_set_ir(&function.parameters[0].set, context)?;
    let codomain = render_set_ir(function.return_set.as_ref(), context)?;
    if function.domain_facts.is_empty() {
        Ok(format!("Litex.Fn {domain} {codomain}"))
    } else {
        Ok(format!(
            "Litex.FnWhere {domain} {codomain} {}",
            render_function_requirement(function, context)?
        ))
    }
}

fn render_function_set(
    function: &LitexToLeanFunctionTypeIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "(Litex.fnTelescopeSet {})",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let render_base_set = |set: &LitexToLeanObjectIr| -> Result<String, String> {
        let rendered = render_set_ir(set, context)?;
        if matches!(set, LitexToLeanObjectIr::Symbol { .. }) {
            Ok(format!("({rendered} : Litex.Set.{{0}})"))
        } else {
            Ok(rendered)
        }
    };
    let domain = render_base_set(&function.parameters[0].set)?;
    let codomain = match function.return_set.as_ref() {
        LitexToLeanObjectIr::FunctionSet { function } => {
            render_nested_function_set(function, context)?
        }
        return_set => render_base_set(return_set)?,
    };
    if function.domain_facts.is_empty() {
        Ok(format!("(Litex.fnSet {domain} {codomain})"))
    } else {
        Ok(format!(
            "(Litex.fnSetWhere {domain} {codomain} {})",
            render_function_requirement(function, context)?
        ))
    }
}

fn render_nested_function_set(
    function: &LitexToLeanFunctionTypeIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "(Litex.fnTelescopeSet {})",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let render_base_set = |set: &LitexToLeanObjectIr| -> Result<String, String> {
        let rendered = render_set_ir(set, context)?;
        if matches!(set, LitexToLeanObjectIr::Symbol { .. }) {
            Ok(format!("({rendered} : Litex.Set.{{0}})"))
        } else {
            Ok(rendered)
        }
    };
    let domain = render_base_set(&function.parameters[0].set)?;
    let codomain = match function.return_set.as_ref() {
        LitexToLeanObjectIr::FunctionSet { function } => {
            render_nested_function_set(function, context)?
        }
        return_set => render_base_set(return_set)?,
    };
    if function.domain_facts.is_empty() {
        Ok(format!("(Litex.fnSet {domain} {codomain})"))
    } else {
        Ok(format!(
            "(Litex.fnSetWhere {domain} {codomain} {})",
            render_function_requirement(function, context)?
        ))
    }
}

fn render_named_function_value(
    definition: &LitexToLeanHaveFnEqualStmtIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(String, bool), String> {
    let function = &definition.function;
    let real_signature = function.parameters.iter().all(|parameter| {
        parameter.set == LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
    }) && function.return_set.as_ref()
        == &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real);

    if function_uses_telescope(function) {
        validate_function_type(function)?;
        let mut binders = Vec::with_capacity(function.parameters.len());
        let mut real_representations = HashMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let suffix = index + 1;
            let alpha = format!("__alpha{suffix}");
            let argument = format!("__arg{suffix}");
            let membership = format!("__arg{suffix}_in");
            let domain = render_set_ir(&parameter.set, context)?;
            binders.push(format!(
                "fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
            ));
            real_representations.insert(
                parameter.symbol_id,
                format!("Litex.In.rep {argument} {membership}"),
            );
        }
        if !function.domain_facts.is_empty() {
            binders.push("fun __arg_domain => ".into());
        }
        if real_signature {
            let body = render_real_function_body_with_parameters(
                &definition.body,
                &real_representations,
                context,
            )?;
            return Ok((format!("{}ULift.up ({body})", binders.concat()), true));
        }
        let (_, _, _, selected_return) = render_function_return_selection(
            &definition.source_body,
            &definition.inferred_premises,
            &definition.return_check,
            context,
        )?;
        return Ok((
            format!("{}ULift.up ({selected_return})", binders.concat()),
            false,
        ));
    }
    validate_unary_function_type(function)?;
    let (body, uses_native_real_body) = if real_signature {
        (
            render_real_function_body(
                &definition.body,
                function.parameters[0].symbol_id,
                "Litex.In.rep __arg __arg_in",
                context,
            )?,
            true,
        )
    } else {
        (
            render_function_return_selection(
                &definition.source_body,
                &definition.inferred_premises,
                &definition.return_check,
                context,
            )?
            .3,
            false,
        )
    };
    if function.domain_facts.is_empty() {
        Ok((
            format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {body} }}"),
            uses_native_real_body,
        ))
    } else {
        Ok((
            format!(
                "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {body} }}"
            ),
            uses_native_real_body,
        ))
    }
}

/// Render the target value for the direct native-real named-function slice.
/// Binder names are the same names installed by the parent Result compiler's
/// child environment, so the nesting of the generated Lean term mirrors the
/// nesting of `SuccessVerifyFunctionDefinitionResult`.
fn render_named_real_function_value_from_result(
    function: &LitexToLeanFunctionTypeIr,
    body: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let real_signature = function.parameters.iter().all(|parameter| {
        parameter.set == LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
    }) && function.return_set.as_ref()
        == &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real);
    if !real_signature {
        return Err("native-real function renderer received a non-real signature".into());
    }
    if function_uses_telescope(function) {
        validate_function_type(function)?;
        let mut binders = Vec::with_capacity(function.parameters.len() + 1);
        let mut parameter_representations = HashMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let suffix = index + 1;
            let alpha = format!("__alpha{suffix}");
            let argument = format!("__arg{suffix}");
            let membership = format!("__arg{suffix}_in");
            let domain = render_set_ir(&parameter.set, context)?;
            binders.push(format!(
                "fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
            ));
            parameter_representations.insert(
                parameter.symbol_id,
                format!("Litex.In.rep {argument} {membership}"),
            );
        }
        if !function.domain_facts.is_empty() {
            binders.push("fun __arg_domain => ".into());
        }
        let body =
            render_real_function_body_with_parameters(body, &parameter_representations, context)?;
        return Ok(format!("{}ULift.up ({body})", binders.concat()));
    }

    validate_unary_function_type(function)?;
    let body = render_real_function_body(
        body,
        function.parameters[0].symbol_id,
        "Litex.In.rep __arg __arg_in",
        context,
    )?;
    if function.domain_facts.is_empty() {
        Ok(format!(
            "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {body} }}"
        ))
    } else {
        Ok(format!(
            "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {body} }}"
        ))
    }
}

fn render_function_return_selection(
    source_body: &Obj,
    inferred_premises: &[LitexToLeanFactIr],
    return_check: &LitexToLeanFactIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(String, String, String, String), String> {
    let mut proof_context = context.clone();
    let mut inferred_lets = Vec::new();
    for (index, inferred) in inferred_premises.iter().enumerate() {
        let proposition = render_fact(&inferred.proposition, &proof_context)?;
        let proof = render_proof(inferred, &proof_context)?;
        let name = format!("__fn_inferred{index}");
        inferred_lets.push(format!("let {name} : {proposition} := ({proof}); "));
        if let Some(fact_id) = inferred.stored_fact_id() {
            proof_context.fact_names.insert(fact_id, name);
            proof_context
                .fact_propositions
                .insert(fact_id, inferred.proposition.clone());
        }
    }
    let source_body = render_obj(source_body, &proof_context)?;
    let return_proof = render_proof(return_check, &proof_context)?;
    let prefix = inferred_lets.concat();
    let selected_return = format!("{prefix}Litex.In.rep {source_body} ({return_proof})");
    Ok((source_body, return_proof, prefix, selected_return))
}

fn render_real_function_body(
    body: &LitexToLeanObjectIr,
    parameter_symbol_id: SymbolId,
    parameter_representation: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_real_function_body_with_parameters(
        body,
        &HashMap::from([(parameter_symbol_id, parameter_representation.to_string())]),
        context,
    )
}

fn render_real_function_body_with_parameters(
    body: &LitexToLeanObjectIr,
    parameter_representations: &HashMap<SymbolId, String>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match body {
        LitexToLeanObjectIr::Symbol { symbol_id, .. }
            if parameter_representations.contains_key(symbol_id) =>
        {
            Ok(parameter_representations[symbol_id].clone())
        }
        LitexToLeanObjectIr::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("({normalized_value} : ℝ)"))
        }
        LitexToLeanObjectIr::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LitexToLeanBuiltinObjectOperatorIr::Add
                    | LitexToLeanBuiltinObjectOperatorIr::Sub
                    | LitexToLeanBuiltinObjectOperatorIr::Mul
                    | LitexToLeanBuiltinObjectOperatorIr::Div
            ) =>
        {
            let left = render_real_function_body_with_parameters(
                &arguments[0],
                parameter_representations,
                context,
            )?;
            let right = render_real_function_body_with_parameters(
                &arguments[1],
                parameter_representations,
                context,
            )?;
            let operator = match operator {
                LitexToLeanBuiltinObjectOperatorIr::Add => "+",
                LitexToLeanBuiltinObjectOperatorIr::Sub => "-",
                LitexToLeanBuiltinObjectOperatorIr::Mul => "*",
                LitexToLeanBuiltinObjectOperatorIr::Div => "/",
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("({left} {operator} {right})"))
        }
        LitexToLeanObjectIr::Symbol { .. } => render_ir_symbol(body, context),
        other => Err(format!(
            "compiler real named-function body does not support {other:?}"
        )),
    }
}

fn render_anonymous_function(
    function: &LitexToLeanAnonymousFunctionIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    validate_function_type(&function.function)?;
    let occurrence = function.source_occurrence_id.ok_or_else(|| {
        "anonymous function has no parser-owned source occurrence identity".to_string()
    })?;
    let certificate = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "anonymous function has no active WD certificate".to_string())?;
    let source_use = certificate
        .source_object_uses
        .iter()
        .find(|source_use| source_use.source_occurrence_id == occurrence)
        .ok_or_else(|| {
            format!(
                "anonymous function occurrence {} has no exact WD object use",
                occurrence.value()
            )
        })?;
    let object = certificate
        .objects
        .iter()
        .find(|object| object.well_defined_obj_id == source_use.well_defined_obj_id)
        .ok_or_else(|| "anonymous function WD object is missing".to_string())?;
    if obj_equality_key(&object.source_object) != function.semantic_key {
        return Err("anonymous function WD object changed its source body or signature".into());
    }
    let scope_id = object
        .owned_binder_scope_id
        .ok_or_else(|| "anonymous function WD object has no owned binder scope".to_string())?;
    let scope = certificate
        .binder_scopes
        .iter()
        .find(|scope| scope.scope_id == scope_id)
        .ok_or_else(|| "anonymous function owned binder scope is missing".to_string())?;

    let mut nested = context.clone();
    let uses_telescope = function_uses_telescope(&function.function);
    let mut binders = Vec::with_capacity(function.function.parameters.len());
    let mut parameter_values = HashMap::new();
    for (parameter_index, parameter) in function.function.parameters.iter().enumerate() {
        let matches = scope
            .premises
            .iter()
            .filter(|premise| {
                matches!(
                    premise.role,
                    WellDefinedBinderPremiseRole::ParameterMembership { .. }
                ) && premise.symbol_id == Some(parameter.symbol_id)
            })
            .collect::<Vec<_>>();
        let [parameter_premise] = matches.as_slice() else {
            return Err(format!(
                "anonymous function requires one exact membership premise for parameter {parameter_index}"
            ));
        };
        let suffix = if uses_telescope {
            (parameter_index + 1).to_string()
        } else {
            String::new()
        };
        let argument = format!("__arg{suffix}");
        let membership = format!("__arg{suffix}_in");
        let domain = render_set_ir(&parameter.set, &nested)?;
        if uses_telescope {
            binders.push(format!(
                "fun {{__alpha{} : Type}} ({argument} : __alpha{}) ({membership} : Litex.In {argument} {domain}) => ",
                parameter_index + 1,
                parameter_index + 1,
            ));
        }
        nested
            .symbol_names
            .insert(parameter.symbol_id, argument.clone());
        nested
            .fact_names
            .insert(parameter_premise.fact_id, membership.clone());
        nested.fact_propositions.insert(
            parameter_premise.fact_id,
            parameter_premise.proposition.clone(),
        );
        if let Some(real) = membership_real_value(&parameter.set, &argument, &membership) {
            nested.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &membership)
        {
            nested
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) = membership_numeric_proof(&parameter.set, &argument, &membership) {
            nested
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
        parameter_values.insert(parameter.symbol_id, (argument, membership));
    }

    let domain_premises = scope
        .premises
        .iter()
        .filter(|premise| matches!(premise.role, WellDefinedBinderPremiseRole::Domain { .. }))
        .collect::<Vec<_>>();
    if domain_premises.len() != function.function.domain_facts.len() {
        return Err("anonymous function binder scope changed its domain-premise count".into());
    }
    for (index, premise) in domain_premises.iter().enumerate() {
        let selector = conjunction_selector(index, domain_premises.len())?;
        let name = if domain_premises.len() == 1 {
            "__arg_domain".into()
        } else {
            format!("__arg_domain{selector}")
        };
        nested.fact_names.insert(premise.fact_id, name);
        nested
            .fact_propositions
            .insert(premise.fact_id, premise.proposition.clone());
    }
    if uses_telescope && !domain_premises.is_empty() {
        binders.push("fun __arg_domain => ".into());
    }

    let mut inferred_lets = Vec::new();
    for (index, inferred) in scope.inferred_premises.iter().enumerate() {
        let proposition = render_fact(&inferred.proposition, &nested)?;
        let proof = render_proof(inferred, &nested)?;
        let name = format!("__anonymous_inferred{index}");
        inferred_lets.push(format!("let {name} : {proposition} := ({proof}); "));
        if let Some(fact_id) = inferred.stored_fact_id() {
            nested.fact_names.insert(fact_id, name);
            nested
                .fact_propositions
                .insert(fact_id, inferred.proposition.clone());
        }
    }

    let [closure] = object.target_requirements.as_slice() else {
        return Err("anonymous function requires one exact return-closure requirement".into());
    };
    let selected_return = match closure.role {
        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
            let closure_fact = certificate
                .facts
                .iter()
                .find(|fact| fact.well_defined_fact_id == closure.well_defined_fact_id)
                .ok_or_else(|| "anonymous function body-membership proof is missing".to_string())?;
            let (body, return_set) = membership_parts(&closure_fact.fact.proposition)?;
            if LitexToLeanObjectIr::lower(body)? != *function.body
                || LitexToLeanObjectIr::lower(return_set)? != *function.function.return_set
            {
                return Err(
                    "anonymous function return closure changed its exact body or carrier".into(),
                );
            }
            format!(
                "Litex.In.rep {} ({})",
                render_obj(body, &nested)?,
                render_proof(&closure_fact.fact, &nested)?
            )
        }
        WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
            parameter_group_index: _,
            parameter_index,
        } => {
            let parameter = function
                .function
                .parameters
                .get(parameter_index)
                .ok_or_else(|| {
                    "anonymous subset closure changed its bound parameter index".to_string()
                })?;
            let (argument, membership) =
                parameter_values.get(&parameter.symbol_id).ok_or_else(|| {
                    "anonymous subset closure lost its parameter evidence".to_string()
                })?;
            format!("Litex.In.rep {argument} {membership}")
        }
        _ => return Err("anonymous function retained an unsupported return-closure route".into()),
    };
    let checked_body = format!("{}{}", inferred_lets.concat(), selected_return);
    let value = if uses_telescope {
        format!("{}ULift.up ({checked_body})", binders.concat())
    } else if function.function.domain_facts.is_empty() {
        format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {checked_body} }}")
    } else {
        format!(
            "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {checked_body} }}"
        )
    };
    Ok(format!(
        "({value} : {})",
        render_function_type(&function.function, context)?
    ))
}

fn render_set_ir(
    object: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LitexToLeanObjectIr::Symbol { symbol_id, name } => context
            .symbol_names
            .get(symbol_id)
            .cloned()
            .ok_or_else(|| format!("unbound compiler set symbol `{name}`")),
        LitexToLeanObjectIr::StandardSet(set) => render_standard_set_ir(*set),
        LitexToLeanObjectIr::SetBuilder(builder) => {
            let base = render_set_ir(builder.set.as_ref(), context)?;
            let parameter = lean_identifier(&builder.name);
            let mut nested = context.clone();
            nested
                .symbol_names
                .insert(builder.symbol_id, parameter.clone());
            if let Some(real) = exact_set_real_value(builder.set.as_ref(), &parameter) {
                nested.numeric_real_values.insert(builder.symbol_id, real);
            }
            if let Some(representation) = exact_set_numeric_value(builder.set.as_ref(), &parameter)
            {
                nested
                    .numeric_representations
                    .insert(builder.symbol_id, representation);
            }
            if let Some(proof) = exact_set_numeric_proof(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_representation_memberships
                    .insert(builder.symbol_id, proof);
            }
            let facts = builder
                .facts
                .iter()
                .map(|fact| render_fact(fact, &nested))
                .collect::<Result<Vec<_>, _>>()?;
            if facts.is_empty() {
                return Err("compiler set builder retained an empty predicate".into());
            }
            Ok(format!(
                "(Litex.setBuilder {base} (fun ({parameter} : {base}.Carrier) => {}))",
                conjunction(&facts)
            ))
        }
        LitexToLeanObjectIr::FunctionSet { function } => render_function_set(function, context),
        other => Err(format!(
            "unsupported compiler function domain/codomain `{other:?}`"
        )),
    }
}

fn render_function_application(
    application: &LitexToLeanFunctionApplicationIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if application.argument_layers.is_empty()
        || application.argument_layers.len() != application.source_argument_layers.len()
        || application
            .argument_layers
            .iter()
            .zip(application.source_argument_layers.iter())
            .any(|(arguments, source_arguments)| {
                arguments.is_empty() || arguments.len() != source_arguments.len()
            })
    {
        return Err(
            "compiler function application changed a retained source argument layer".into(),
        );
    }
    let Obj::FnObj(source_application) = &application.source_application else {
        return Err("function application retained a non-application source object".into());
    };
    let certificate = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "function application has no active WD certificate".to_string())?;
    let source_use = certificate
        .source_object_uses
        .iter()
        .find(|source_use| source_use.source_occurrence_id == application.source_occurrence_id)
        .ok_or_else(|| {
            format!(
                "function application occurrence {} has no exact WD object use",
                application.source_occurrence_id.value()
            )
        })?;
    let object = certificate
        .objects
        .iter()
        .find(|object| object.well_defined_obj_id == source_use.well_defined_obj_id)
        .ok_or_else(|| "function application WD object is missing".to_string())?;
    if obj_equality_key(&object.source_object) != obj_equality_key(&application.source_application)
    {
        return Err("function application WD object changed its source occurrence".into());
    }

    let layer_count = application.argument_layers.len();
    let mut layer_objects = vec![None; layer_count];
    let mut layer_object = object;
    for layer_index in (0..layer_count).rev() {
        let source_prefix = source_application.prefix_obj(layer_index + 1);
        if obj_equality_key(&layer_object.source_object) != obj_equality_key(&source_prefix) {
            return Err(format!(
                "application layer {layer_index} changed its verifier-owned source prefix"
            ));
        }
        layer_objects[layer_index] = Some(layer_object);
        if layer_index == 0 {
            continue;
        }
        let prefix_uses = layer_object
            .child_uses
            .iter()
            .filter(|child| {
                child.role
                    == (WellDefinedObjChildRole::FunctionPrefix {
                        through_layer_index: layer_index - 1,
                    })
            })
            .collect::<Vec<_>>();
        let [prefix_use] = prefix_uses.as_slice() else {
            return Err(format!(
                "application layer {layer_index} requires one exact WD prefix child"
            ));
        };
        layer_object = certificate
            .objects
            .iter()
            .find(|candidate| candidate.well_defined_obj_id == prefix_use.obj_id)
            .ok_or_else(|| {
                format!("application layer {layer_index} references a missing WD prefix object")
            })?;
    }

    let root_contracts = object.function_contracts.clone();
    let (mut function, mut head, mut membership_proof, mut direct) = match application.head.as_ref()
    {
        LitexToLeanObjectIr::Symbol {
            symbol_id: head_symbol_id,
            ..
        } => {
            let [WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)] =
                root_contracts.as_slice()
            else {
                return Err(
                    "named application requires one verifier-selected membership FactId".into(),
                );
            };
            let binding = context
                .function_bindings
                .get(contract_fact_id)
                .ok_or_else(|| {
                    format!("unavailable function membership FactId `{contract_fact_id}`")
                })?;
            if *head_symbol_id != binding.symbol_id {
                return Err("function membership FactId belongs to another head symbol".into());
            }
            (
                binding.function.clone(),
                render_ir_symbol(application.head.as_ref(), context)?,
                binding.membership_proof_name.clone(),
                binding.direct,
            )
        }
        LitexToLeanObjectIr::AnonymousFunction(anonymous) => {
            if !root_contracts.is_empty() {
                return Err("anonymous application retained an unexpected named contract".into());
            }
            let head_uses = layer_objects[0]
                .ok_or_else(|| "anonymous application lost its first WD layer".to_string())?
                .child_uses
                .iter()
                .filter(|child| child.role == WellDefinedObjChildRole::FunctionHead)
                .collect::<Vec<_>>();
            let [head_use] = head_uses.as_slice() else {
                return Err(
                    "anonymous application requires one exact verifier-owned head child".into(),
                );
            };
            let head_object = certificate
                .objects
                .iter()
                .find(|candidate| candidate.well_defined_obj_id == head_use.obj_id)
                .ok_or_else(|| "anonymous application WD head object is missing".to_string())?;
            if obj_equality_key(&head_object.source_object) != anonymous.semantic_key {
                return Err("anonymous application changed its verifier-owned head".into());
            }
            let head = render_anonymous_function(anonymous, context)?;
            let function_set = render_function_set(&anonymous.function, context)?;
            (
                anonymous.function.clone(),
                head.clone(),
                format!("(Litex.In.own {function_set} {head})"),
                true,
            )
        }
        _ => return Err("compiler function application requires a named or anonymous head".into()),
    };
    let mut layer_lets = Vec::new();
    for layer_index in 0..layer_count {
        validate_function_type(&function)?;
        let layer_object = layer_objects[layer_index]
            .ok_or_else(|| format!("application layer {layer_index} lost its WD object"))?;
        if layer_object.function_contracts != root_contracts {
            return Err(format!(
                "application layer {layer_index} changed its root function contract"
            ));
        }
        if function.parameters.len() != application.argument_layers[layer_index].len() {
            return Err(format!(
                "application layer {layer_index} expected {} parameters, retained {} arguments",
                function.parameters.len(),
                application.argument_layers[layer_index].len()
            ));
        }
        for (source_argument, retained_argument) in application.source_argument_layers[layer_index]
            .iter()
            .zip(application.argument_layers[layer_index].iter())
        {
            if LitexToLeanObjectIr::lower(source_argument)? != *retained_argument {
                return Err(format!(
                    "application layer {layer_index} changed its retained argument IR"
                ));
            }
        }

        let mut argument_requirements = vec![None; function.parameters.len()];
        let mut domain_requirements = vec![None; function.domain_facts.len()];
        for requirement in &layer_object.target_requirements {
            match requirement.role {
                WellDefinednessRequirementRole::FunctionArgumentMembership {
                    layer_index: retained_layer_index,
                    parameter_index,
                } if retained_layer_index == layer_index
                    && parameter_index < argument_requirements.len() =>
                {
                    if argument_requirements[parameter_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate argument-membership requirement {parameter_index}"
                        ));
                    }
                }
                WellDefinednessRequirementRole::FunctionDomain {
                    layer_index: retained_layer_index,
                    domain_index,
                } if retained_layer_index == layer_index
                    && domain_index < domain_requirements.len() =>
                {
                    if domain_requirements[domain_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate domain requirement {domain_index}"
                        ));
                    }
                }
                role => {
                    return Err(format!(
                        "application layer {layer_index} retained an unexpected target requirement {role:?}"
                    ));
                }
            }
        }
        if argument_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked argument-membership requirement"
            ));
        }
        if domain_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked source-domain requirement"
            ));
        }
        let mut nested = context.clone();
        // Domain verification in Result is about the original source
        // arguments. The target telescope may separately observe a
        // heterogeneous parameter through its membership proof, so keep a
        // source-facing rendering context for exact Result validation.
        let mut source_domain_nested = context.clone();
        let mut arguments = Vec::with_capacity(function.parameters.len());
        let mut argument_memberships = Vec::with_capacity(function.parameters.len());
        for (parameter_index, ((parameter, source_argument), requirement)) in function
            .parameters
            .iter()
            .zip(application.source_argument_layers[layer_index].iter())
            .zip(argument_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("argument requirements checked above");
            let argument_fact = certificate
                .facts
                .iter()
                .find(|fact| fact.well_defined_fact_id == requirement.well_defined_fact_id)
                .ok_or_else(|| {
                    format!(
                        "application layer {layer_index} argument-membership proof {parameter_index} is missing"
                    )
                })?;
            let argument = render_obj(source_argument, context)?;
            let expected_argument_membership = format!(
                "Litex.In {argument} {}",
                render_set_ir(&parameter.set, &nested)?
            );
            let retained_argument_membership =
                render_fact(&argument_fact.fact.proposition, context)?;
            if retained_argument_membership != expected_argument_membership {
                return Err(format!(
                    "application layer {layer_index} expected `{expected_argument_membership}`, retained `{retained_argument_membership}`"
                ));
            }
            let argument_membership = render_proof(&argument_fact.fact, context)?;
            arguments.push(argument.clone());
            argument_memberships.push(argument_membership.clone());
            nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .numeric_representations
                .insert(parameter.symbol_id, argument.clone());
            if let Some(real) = membership_real_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested.numeric_real_values.insert(parameter.symbol_id, real);
            }
            if let Some(representation) = membership_numeric_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representations
                    .insert(parameter.symbol_id, representation);
            }
            if let Some(proof) = membership_numeric_proof(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representation_memberships
                    .insert(parameter.symbol_id, proof);
            }
        }
        let mut domain_proofs = Vec::with_capacity(domain_requirements.len());
        for (domain_index, (source_fact, requirement)) in function
            .domain_facts
            .iter()
            .zip(domain_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("domain requirements checked above");
            let domain_fact = certificate
                .facts
                .iter()
                .find(|fact| fact.well_defined_fact_id == requirement.well_defined_fact_id)
                .ok_or_else(|| {
                    format!(
                        "application layer {layer_index} domain proof {domain_index} is missing"
                    )
                })?;
            let expected = render_fact(source_fact, &source_domain_nested)?;
            let retained = render_fact(&domain_fact.fact.proposition, context)?;
            if expected != retained {
                return Err(format!(
                    "application layer {layer_index} expected domain clause {expected}, retained {retained}"
                ));
            }
            let retained_proof = render_proof(&domain_fact.fact, context)?;
            if positive_natural_parameter_less_equal_natural_bound(&function, source_fact)?
                .is_some()
            {
                domain_proofs.push(format!(
                    "Litex.positiveNaturalParameterLessEqualNaturalBoundOfComplex ({retained_proof})"
                ));
            } else {
                domain_proofs.push(retained_proof);
            }
        }

        let application_term = if !function_uses_telescope(&function) {
            let apply = match (direct, domain_proofs.is_empty()) {
                (true, true) => "Litex.fnApplyOwn",
                (false, true) => "Litex.fnApply",
                (true, false) => "Litex.fnApplyWhereOwn",
                (false, false) => "Litex.fnApplyWhere",
            };
            let argument = &arguments[0];
            let argument_membership = &argument_memberships[0];
            if domain_proofs.is_empty() {
                format!("({apply} {head} {membership_proof} {argument} ({argument_membership}))")
            } else {
                let domain_proof = if domain_proofs.len() == 1 {
                    domain_proofs[0].clone()
                } else {
                    format!("⟨{}⟩", domain_proofs.join(", "))
                };
                format!(
                    "({apply} {head} {membership_proof} {argument} ({argument_membership}) ({domain_proof}))"
                )
            }
        } else {
            let apply = if direct {
                "Litex.fnTelescopeApplyOwn"
            } else {
                "Litex.fnTelescopeApply"
            };
            let mut term = format!("({apply} {head} {membership_proof})");
            for (argument, argument_membership) in arguments.iter().zip(argument_memberships.iter())
            {
                term = format!("({term} {argument} ({argument_membership}))");
            }
            if !domain_proofs.is_empty() {
                let domain_proof = if domain_proofs.len() == 1 {
                    domain_proofs[0].clone()
                } else {
                    format!("⟨{}⟩", domain_proofs.join(", "))
                };
                term = format!("({term} ({domain_proof}))");
            }
            format!("({term}).down")
        };

        if layer_index + 1 == layer_count {
            head = application_term;
            continue;
        }
        let LitexToLeanObjectIr::FunctionSet {
            function: next_function,
        } = function.return_set.as_ref()
        else {
            return Err(format!(
                "application layer {layer_index} does not return the next function set"
            ));
        };
        if layer_object.intrinsic_result_set.as_ref() != Some(function.return_set.as_ref()) {
            return Err(format!(
                "application layer {layer_index} lost its exact verifier-owned result set"
            ));
        }
        let next_function_set = render_function_set(next_function, context)?;
        let layer_name = format!("__fn_layer{}", layer_index + 1);
        layer_lets.push(format!("(let {layer_name} := {application_term}; "));
        head = layer_name;
        membership_proof = format!("(Litex.In.own {next_function_set} {head})");
        function = next_function.as_ref().clone();
        direct = true;
    }
    Ok(format!(
        "{}{}{}",
        layer_lets.concat(),
        head,
        ")".repeat(layer_lets.len())
    ))
}

fn render_ir_symbol(
    object: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LitexToLeanObjectIr::Symbol { symbol_id, name } = object else {
        return Err("expected a compiler symbol".into());
    };
    context
        .symbol_names
        .get(symbol_id)
        .cloned()
        .ok_or_else(|| format!("unbound compiler symbol `{name}`"))
}

fn render_native_object_ir(
    object: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_object_ir(object, context)
}

fn render_object_ir(
    object: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LitexToLeanObjectIr::Symbol { .. } => render_ir_symbol(object, context),
        LitexToLeanObjectIr::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("({normalized_value} : ℂ)"))
        }
        LitexToLeanObjectIr::Constant(constant) => Ok(match constant {
            LitexToLeanConstantObjectIr::ImaginaryUnit => "Complex.I".into(),
            LitexToLeanConstantObjectIr::EulerNumber => "((Real.exp 1 : ℝ) : ℂ)".into(),
            LitexToLeanConstantObjectIr::Pi => "((Real.pi : ℝ) : ℂ)".into(),
        }),
        LitexToLeanObjectIr::StandardSet(set) => render_standard_set_ir(*set),
        LitexToLeanObjectIr::FunctionSet { function } => render_function_set(function, context),
        LitexToLeanObjectIr::SetBuilder(_) => render_set_ir(object, context),
        LitexToLeanObjectIr::AnonymousFunction(function) => {
            render_anonymous_function(function, context)
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            render_function_application(application, context)
        }
        LitexToLeanObjectIr::Range { start, end } => Ok(format!(
            "(Litex.range {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LitexToLeanObjectIr::ClosedRange { start, end } => Ok(format!(
            "(Litex.closedRange {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LitexToLeanObjectIr::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => Ok(format!(
            "(Litex.generalCart {} {} {})",
            render_object_ir(index_set, context)?,
            render_object_ir(family_set, context)?,
            render_object_ir(family_function, context)?
        )),
        LitexToLeanObjectIr::SequenceSet { values, length } => match length {
            Some(length) => Ok(format!(
                "(Litex.finiteSequenceSet.{{0}} {} {})",
                render_set_ir(values, context)?,
                render_natural_endpoint(length)?
            )),
            None => Ok(format!(
                "(Litex.sequenceSet {})",
                render_set_ir(values, context)?
            )),
        },
        LitexToLeanObjectIr::MatrixSet {
            values,
            row_count,
            column_count,
        } => Ok(format!(
            "(Litex.matrixSet.{{0}} {} {} {})",
            render_set_ir(values, context)?,
            render_natural_endpoint(row_count)?,
            render_natural_endpoint(column_count)?,
        )),
        LitexToLeanObjectIr::Aggregate {
            kind, arguments, ..
        } => render_aggregate_object(*kind, arguments, context),
        LitexToLeanObjectIr::TupleDimension(tuple) => Ok(format!(
            "(Litex.tupleDim {})",
            render_object_ir(tuple, context)?
        )),
        LitexToLeanObjectIr::IndexedAccess { object, index } => {
            render_literal_indexed_access(object, index, context)
        }
        LitexToLeanObjectIr::BuiltinApp {
            operator,
            arguments,
            ..
        } => render_builtin_object(*operator, arguments, context),
        LitexToLeanObjectIr::Collection {
            constructor: LitexToLeanCollectionObjectIr::Tuple,
            items,
            ..
        } => render_typed_spine(items, context),
        LitexToLeanObjectIr::Collection {
            constructor: LitexToLeanCollectionObjectIr::SequenceLiteral,
            items,
            ..
        } => Ok(format!(
            "(Litex.SequenceLiteral.mk {})",
            render_typed_spine(items, context)?
        )),
        LitexToLeanObjectIr::Collection {
            constructor: LitexToLeanCollectionObjectIr::ListSet,
            items,
            ..
        } => render_list_set(items, context),
        other => Err(format!(
            "unsupported native object definition value `{other:?}`"
        )),
    }
}

fn render_list_set(
    items: &[LitexToLeanObjectIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut set = "Litex.Set.empty".to_string();
    for item in items.iter().rev() {
        set = format!(
            "(Litex.Set.coproduct (Litex.Set.singleton {}) {set})",
            render_object_ir(item, context)?
        );
    }
    Ok(set)
}

fn render_list_set_finiteness(
    items: &[LitexToLeanObjectIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut set = "Litex.Set.empty".to_string();
    let mut proof = "Litex.Set.empty_finite".to_string();
    for item in items.iter().rev() {
        let item = render_object_ir(item, context)?;
        proof = format!(
            "Litex.Set.coproduct_finite (Litex.Set.singleton {item}) {set} (Litex.Set.singleton_finite {item}) ({proof})"
        );
        set = format!("(Litex.Set.coproduct (Litex.Set.singleton {item}) {set})");
    }
    Ok(proof)
}

fn render_integer_endpoint(
    object: &LitexToLeanObjectIr,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LitexToLeanObjectIr::Number { normalized_value } = object else {
        return Err("integer range endpoints currently require closed integer numerals".into());
    };
    if normalized_value.parse::<i128>().is_err() {
        return Err(format!(
            "integer range endpoint `{normalized_value}` is not a closed integer numeral"
        ));
    }
    Ok(format!("({normalized_value} : ℤ)"))
}

fn render_natural_endpoint(object: &LitexToLeanObjectIr) -> Result<String, String> {
    let LitexToLeanObjectIr::Number { normalized_value } = object else {
        return Err("finite sequence length currently requires a closed natural numeral".into());
    };
    if normalized_value.is_empty()
        || !normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(format!(
            "finite sequence length `{normalized_value}` is not a natural numeral"
        ));
    }
    Ok(format!("({normalized_value} : Nat)"))
}

fn render_typed_spine(
    items: &[LitexToLeanObjectIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut tail = "Litex.HNil.nil".to_string();
    for item in items.iter().rev() {
        tail = format!(
            "(Litex.HCons.mk {} {tail})",
            render_object_ir(item, context)?
        );
    }
    Ok(tail)
}

fn render_aggregate_object(
    kind: LitexToLeanAggregateObjectIr,
    arguments: &[LitexToLeanObjectIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (name, arity) = match kind {
        LitexToLeanAggregateObjectIr::Sum => ("Litex.sum", 3),
        LitexToLeanAggregateObjectIr::Product => ("Litex.product", 3),
        LitexToLeanAggregateObjectIr::FiniteSetSum => ("Litex.finiteSetSum", 2),
        LitexToLeanAggregateObjectIr::FiniteSetProduct => ("Litex.finiteSetProduct", 2),
        LitexToLeanAggregateObjectIr::Reduce => ("Litex.reduce", 5),
        LitexToLeanAggregateObjectIr::FiniteSetReduce => ("Litex.finiteSetReduce", 4),
    };
    if arguments.len() != arity {
        return Err(format!(
            "aggregate `{kind:?}` changed its exact source arity"
        ));
    }
    let rendered = arguments
        .iter()
        .map(|argument| render_object_ir(argument, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("({name} {})", rendered.join(" ")))
}

fn render_literal_indexed_access(
    object: &LitexToLeanObjectIr,
    index: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LitexToLeanObjectIr::Symbol { symbol_id, .. } = object {
        if let Some(binding) = context.indexed_tuple_bindings.get(symbol_id) {
            let tuple = render_object_ir(object, context)?;
            let exact_index = match index {
                LitexToLeanObjectIr::Symbol {
                    symbol_id: index_symbol_id,
                    ..
                } => context
                    .exact_tuple_indices
                    .get(index_symbol_id)
                    .cloned()
                    .ok_or_else(|| {
                        "indexed tuple projection has no exact checked index representative"
                            .to_string()
                    })?,
                LitexToLeanObjectIr::Number { normalized_value } => {
                    let value = normalized_value.parse::<usize>().map_err(|_| {
                        "indexed tuple projection index is not a natural numeral".to_string()
                    })?;
                    if value == 0 || value > binding.dimension {
                        return Err(
                            "indexed tuple projection index is outside its checked dimension"
                                .into(),
                        );
                    }
                    format!("⟨({value} : ℤ), by norm_num⟩")
                }
                _ => {
                    return Err(
                        "indexed tuple projection needs a checked range representative".into(),
                    );
                }
            };
            return Ok(format!("(Litex.indexedTupleAt {tuple} {exact_index})"));
        }
    }
    let LitexToLeanObjectIr::Number { normalized_value } = index else {
        return Err("literal tuple access requires a closed natural index".into());
    };
    let index = normalized_value
        .parse::<usize>()
        .map_err(|_| "literal tuple access has an invalid natural index".to_string())?;
    let LitexToLeanObjectIr::Collection { items, .. } = object else {
        return Err(
            "generic heterogeneous indexed access needs a checked projection recipe".into(),
        );
    };
    let item = items.get(index.saturating_sub(1)).ok_or_else(|| {
        "literal tuple access index is outside the retained source arity".to_string()
    })?;
    render_object_ir(item, context)
}

fn render_builtin_object(
    operator: LitexToLeanBuiltinObjectOperatorIr,
    arguments: &[LitexToLeanObjectIr],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let binary_symbol = match operator {
        LitexToLeanBuiltinObjectOperatorIr::Add => Some("+"),
        LitexToLeanBuiltinObjectOperatorIr::Sub => Some("-"),
        LitexToLeanBuiltinObjectOperatorIr::Mul => Some("*"),
        LitexToLeanBuiltinObjectOperatorIr::Div => Some("/"),
        _ => None,
    };
    if let Some(symbol) = binary_symbol {
        let [left, right] = arguments else {
            return Err(format!("numeric operator `{operator:?}` changed its arity"));
        };
        return Ok(format!(
            "({} {symbol} {})",
            render_numeric_object_ir(left, context)?,
            render_numeric_object_ir(right, context)?
        ));
    }
    match (operator, arguments) {
        (LitexToLeanBuiltinObjectOperatorIr::Union, [left, right]) => Ok(format!(
            "(Litex.union {} {})",
            render_object_ir(left, context)?,
            render_object_ir(right, context)?
        )),
        (LitexToLeanBuiltinObjectOperatorIr::Intersect, [left, right]) => Ok(format!(
            "(Litex.intersect {} {})",
            render_object_ir(left, context)?,
            render_object_ir(right, context)?
        )),
        (LitexToLeanBuiltinObjectOperatorIr::SetMinus, [left, right]) => Ok(format!(
            "(Litex.setMinus {} {})",
            render_object_ir(left, context)?,
            render_object_ir(right, context)?
        )),
        (LitexToLeanBuiltinObjectOperatorIr::BigUnion, [family]) => Ok(format!(
            "(Litex.bigUnion {})",
            render_object_ir(family, context)?
        )),
        (LitexToLeanBuiltinObjectOperatorIr::BigIntersect, [family]) => Ok(format!(
            "(Litex.bigIntersect {})",
            render_object_ir(family, context)?
        )),
        (LitexToLeanBuiltinObjectOperatorIr::PowerSet, [base]) => Ok(format!(
            "(Litex.powerSet {})",
            render_object_ir(base, context)?
        )),
        _ => Err(format!(
            "unsupported typed builtin object `{operator:?}` with {} arguments",
            arguments.len()
        )),
    }
}

fn render_numeric_object_ir(
    object: &LitexToLeanObjectIr,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LitexToLeanObjectIr::Symbol { symbol_id, .. } = object {
        if let Some(value) = context.numeric_representations.get(symbol_id) {
            return Ok(value.clone());
        }
    }
    render_object_ir(object, context)
}

fn parameter_set(param_type: &ParamType) -> Result<&Obj, String> {
    match param_type {
        ParamType::Obj(set) => Ok(set),
        _ => Err(format!(
            "unsupported compiler parameter type `{param_type}`"
        )),
    }
}

fn render_standard_set_ir(set: LitexToLeanStandardSetIr) -> Result<String, String> {
    let name = match set {
        LitexToLeanStandardSetIr::PositiveNatural => "Litex.NPos",
        LitexToLeanStandardSetIr::Natural => "Litex.N",
        LitexToLeanStandardSetIr::Integer => "Litex.Z",
        LitexToLeanStandardSetIr::Rational => "Litex.Q",
        LitexToLeanStandardSetIr::Real => "Litex.R",
        LitexToLeanStandardSetIr::Complex => "Litex.C",
        LitexToLeanStandardSetIr::PositiveReal => "Litex.RPos",
        LitexToLeanStandardSetIr::NonzeroInteger => "Litex.ZStar",
        LitexToLeanStandardSetIr::NonzeroRational => "Litex.QStar",
        LitexToLeanStandardSetIr::NonzeroReal => "Litex.RStar",
        LitexToLeanStandardSetIr::NonzeroComplex => "Litex.CStar",
        other => return Err(format!("unsupported compiler standard set `{other:?}`")),
    };
    Ok(name.into())
}

fn render_standard_set(set: StandardSet) -> Result<&'static str, String> {
    match set {
        StandardSet::N => Ok("Litex.N"),
        StandardSet::NPos => Ok("Litex.NPos"),
        StandardSet::Z => Ok("Litex.Z"),
        StandardSet::ZStar => Ok("Litex.ZStar"),
        StandardSet::Q => Ok("Litex.Q"),
        StandardSet::QStar => Ok("Litex.QStar"),
        StandardSet::R => Ok("Litex.R"),
        StandardSet::RPos => Ok("Litex.RPos"),
        StandardSet::RStar => Ok("Litex.RStar"),
        StandardSet::C => Ok("Litex.C"),
        StandardSet::CStar => Ok("Litex.CStar"),
        _ => Err(format!("unsupported compiler standard set `{set}`")),
    }
}

fn membership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected membership fact, found `{fact}`")),
    }
}

fn subset_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(fact)) => Ok((&fact.left, &fact.right)),
        Fact::AtomicFact(AtomicFact::SupersetFact(fact)) => Ok((&fact.right, &fact.left)),
        _ => Err(format!("expected subset fact, found `{fact}`")),
    }
}

fn finite_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected finite-set fact, found `{fact}`")),
    }
}

fn nonempty_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected nonempty-set fact, found `{fact}`")),
    }
}

fn nonmembership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotInFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected non-membership fact, found `{fact}`")),
    }
}

fn equality_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected equality fact, found `{fact}`")),
    }
}

fn not_equal_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected not-equality fact, found `{fact}`")),
    }
}

fn less_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::LessFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected less-than fact, found `{fact}`")),
    }
}

fn less_equal_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::LessEqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected less-equal fact, found `{fact}`")),
    }
}

fn positive_order_parts(fact: &Fact, strict: bool) -> Result<(&Obj, &Obj), String> {
    match (strict, fact) {
        (true, Fact::AtomicFact(AtomicFact::LessFact(fact))) => Ok((&fact.left, &fact.right)),
        (true, Fact::AtomicFact(AtomicFact::GreaterFact(fact))) => Ok((&fact.right, &fact.left)),
        (false, Fact::AtomicFact(AtomicFact::LessEqualFact(fact))) => Ok((&fact.left, &fact.right)),
        (false, Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact))) => {
            Ok((&fact.right, &fact.left))
        }
        (true, _) => Err(format!(
            "expected strict positive-order fact, found `{fact}`"
        )),
        (false, _) => Err(format!(
            "expected non-strict positive-order fact, found `{fact}`"
        )),
    }
}

fn order_relation_parts(fact: &Fact) -> Result<(&Obj, &Obj, bool), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::LessFact(fact)) => Ok((&fact.left, &fact.right, true)),
        Fact::AtomicFact(AtomicFact::GreaterFact(fact)) => Ok((&fact.right, &fact.left, true)),
        Fact::AtomicFact(AtomicFact::LessEqualFact(fact)) => Ok((&fact.left, &fact.right, false)),
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact)) => {
            Ok((&fact.right, &fact.left, false))
        }
        _ => Err(format!(
            "expected positive ordered relation, found `{fact}`"
        )),
    }
}

fn conjunction(facts: &[String]) -> String {
    match facts {
        [] => "True".to_string(),
        [only] => only.clone(),
        _ => facts.join(" ∧ "),
    }
}

fn conjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    match fact {
        Fact::AndFact(and_fact) => Ok(and_fact.facts.iter().cloned().map(Fact::from).collect()),
        Fact::ChainFact(chain_fact) => chain_fact
            .facts()
            .map(|facts| facts.into_iter().map(Fact::from).collect())
            .map_err(|error| format!("invalid retained relation chain: {error:?}")),
        _ => Err(format!(
            "expected conjunction or relation chain, found `{fact}`"
        )),
    }
}

fn disjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    let Fact::OrFact(or_fact) = fact else {
        return Err(format!("expected disjunction, found `{fact}`"));
    };
    Ok(or_fact.facts.iter().cloned().map(Fact::from).collect())
}

fn right_associated_conjunction_proof(proofs: &[String]) -> Result<String, String> {
    let Some(last) = proofs.last() else {
        return Err("conjunction introduction retained no component proofs".into());
    };
    let mut result = last.clone();
    for proof in proofs[..proofs.len() - 1].iter().rev() {
        result = format!("⟨{proof}, {result}⟩");
    }
    Ok(result)
}

fn right_associated_disjunction_injection(
    proof: String,
    selected_index: usize,
    count: usize,
) -> Result<String, String> {
    if count == 0 || selected_index >= count {
        return Err("disjunction introduction selected an out-of-range branch".into());
    }
    if count == 1 {
        return Ok(proof);
    }
    let mut result = if selected_index + 1 < count {
        format!("Or.inl ({proof})")
    } else {
        proof
    };
    for _ in 0..selected_index {
        result = format!("Or.inr ({result})");
    }
    Ok(result)
}

fn conjunction_projection(source: &str, index: usize, count: usize) -> Result<String, String> {
    if count == 0 || index >= count {
        return Err("conjunction projection selected an out-of-range component".into());
    }
    if count == 1 {
        return Ok(source.to_string());
    }
    let mut projection = source.to_string();
    for _ in 0..index {
        projection.push_str(".2");
    }
    if index + 1 < count {
        projection.push_str(".1");
    }
    Ok(projection)
}

fn lean_identifier(source: &str) -> String {
    let mut result = source
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    if result.is_empty() {
        result.push('_');
    }
    result
}

fn indent_lines(text: &str, spaces: usize) -> String {
    let indentation = " ".repeat(spaces);
    text.lines()
        .map(|line| format!("{indentation}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::rule_schema::{RuleFingerprint, RuleId};

    #[test]
    fn nested_compiler_environment_inherits_outer_bindings_without_leaking_back() {
        let outer_fact_id = FactId::new(1);
        let inner_fact_id = FactId::new(2);
        let mut outer = StmtResultToLeanCompilerEnvironmentStack::default();
        outer
            .fact_names
            .insert(outer_fact_id, "__outer".to_string());

        let mut inner = outer.clone();
        inner.push_inherited_environment();
        assert_eq!(inner.environments.len(), 2);
        assert_eq!(
            inner.fact_names.get(&outer_fact_id),
            Some(&"__outer".to_string())
        );
        inner
            .fact_names
            .insert(inner_fact_id, "__inner".to_string());

        assert!(!outer.fact_names.contains_key(&inner_fact_id));
        assert_eq!(
            inner.fact_names.get(&inner_fact_id),
            Some(&"__inner".to_string())
        );
        inner.pop_local_environment();
        assert_eq!(inner.environments.len(), 1);
        assert!(!inner.fact_names.contains_key(&inner_fact_id));
        assert_eq!(
            inner.fact_names.get(&outer_fact_id),
            Some(&"__outer".to_string())
        );
    }

    #[test]
    fn failed_local_result_compilation_restores_the_outer_compiler_layer() {
        let outer_fact_id = FactId::new(1);
        let mut compiler = StmtResultToLeanCompiler::new("local_failure.lit");
        compiler.declarations.push("outer declaration".into());
        compiler.next_fact_name_index = 7;
        compiler.next_sketch_namespace_index = 3;
        compiler
            .environment_stack
            .fact_names
            .insert(outer_fact_id, "__outer".into());

        let unknown: StmtResult =
            UnknownGenericStmtResult::new_with_detail("deliberate local compiler failure".into())
                .into();
        let error = compiler
            .compile_stmt_results_in_new_local_environment(&[unknown])
            .expect_err("unknown local result must fail closed");

        assert!(error.contains("cannot compile unknown result"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations, ["outer declaration"]);
        assert_eq!(compiler.next_fact_name_index, 7);
        assert_eq!(compiler.next_sketch_namespace_index, 3);
        assert_eq!(
            compiler.environment_stack.fact_names.get(&outer_fact_id),
            Some(&"__outer".to_string())
        );
    }

    fn execute_closed_natural_membership() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "2 + 3 $in N\n",
            "direct_closed_membership.lit",
        )
        .expect("execute closed natural membership")
    }

    fn closed_natural_membership_result_mut(
        results: &mut [StmtResult],
    ) -> &mut SuccessFactStmtResult {
        let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
            panic!("expected one successful factual result")
        };
        result
    }

    #[test]
    fn direct_closed_membership_compiler_rejects_corrupted_evaluation_tree() {
        let mut results = execute_closed_natural_membership();
        let result = closed_natural_membership_result_mut(&mut results);
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test result has one proof owner");
        let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
            panic!("expected builtin proof")
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = &mut proof.evidence
        else {
            panic!("expected closed membership evidence")
        };
        evidence.evaluation.value = Number::new("6".to_string());

        let error = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted evaluation must fail closed");
        assert!(error.contains("evaluation changed its expression or value"));
    }

    #[test]
    fn direct_closed_membership_compiler_rejects_corrupted_infer_fact_id() {
        let mut results = execute_closed_natural_membership();
        let result = closed_natural_membership_result_mut(&mut results);
        result.store.infers.rule_applications[0].premises[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted infer citation must fail closed");
        assert!(error.contains("exact stored source FactId"));
    }

    #[test]
    fn direct_closed_membership_compiler_ignores_diagnostic_label_text() {
        let original = execute_closed_natural_membership();
        let original_lean = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
            .compile_stmt_results_to_lean_source(&original)
            .expect("compile original result");

        let mut renamed = execute_closed_natural_membership();
        let result = closed_natural_membership_result_mut(&mut renamed);
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test result has one proof owner");
        let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
            panic!("expected builtin proof")
        };
        proof.msg = "display text is not compiler evidence".to_string();
        let renamed_lean = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
            .compile_stmt_results_to_lean_source(&renamed)
            .expect("compile result after diagnostic-only change");

        assert_eq!(renamed_lean, original_lean);
    }

    fn rename_object_choice_nonempty_diagnostic_label(results: &mut [StmtResult]) {
        let Some(StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(choice),
        ))) = results.first_mut()
        else {
            panic!("expected object-choice statement result")
        };
        let verification = choice
            .verification
            .as_mut()
            .expect("object choice retains verification result");
        let nonempty = verification.groups[0]
            .nonempty_check
            .as_deref_mut()
            .expect("standard carrier retains nonempty check");
        let factual = nonempty
            .factual_success_mut()
            .expect("nonempty check is factual");
        let verification = std::rc::Rc::get_mut(&mut factual.verification)
            .expect("test nonempty result has one proof owner");
        let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
            panic!("expected standard-set builtin proof")
        };
        proof.msg = "diagnostic label is not semantic input".into();
    }

    #[test]
    fn direct_object_choice_compiler_uses_typed_child_evidence_not_its_label() {
        const SOURCE: &str = "have chosen R\nchosen $in R\n";
        let original = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice");
        let original_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
            .compile_stmt_results_to_lean_source(&original)
            .expect("compile object choice");

        let mut renamed = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice again");
        rename_object_choice_nonempty_diagnostic_label(&mut renamed);
        let renamed_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
            .compile_stmt_results_to_lean_source(&renamed)
            .expect("compile object choice after diagnostic-only mutation");

        assert_eq!(renamed_lean, original_lean);
        assert!(original_lean.contains("Classical.choice (Litex.Rules.realNonempty)"));
        assert!(original_lean.contains("Litex.In.own Litex.R chosen"));
    }

    fn execute_single_existential_witness() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\n",
            "direct_existential_witness.lit",
        )
        .expect("execute one-witness existential introduction")
    }

    fn single_existential_witness_result_mut(
        results: &mut [StmtResult],
    ) -> &mut SuccessWitnessExistFactResult {
        let [StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessExistFact(result),
        ))] = results
        else {
            panic!("expected one successful existential-witness result")
        };
        result
    }

    #[test]
    fn existential_witness_compiles_directly_from_named_recursive_children() {
        let mut results = execute_single_existential_witness();
        let result = single_existential_witness_result_mut(&mut results);
        let local_fact_id = result
            .verification
            .as_ref()
            .expect("witness retains verification")
            .proof_steps[0]
            .factual_success()
            .expect("witness proof step is factual")
            .store
            .fact_id
            .expect("witness proof step retains its local FactId");
        let outer_fact_id = result.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("witness outer store retains its FactId");

        let mut compiler = StmtResultToLeanCompiler::new("direct_existential_witness.lit");
        assert!(compiler
            .compile_witness_exist_fact_stmt_result_to_lean_source(result)
            .expect("direct existential-witness compilation succeeds"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&local_fact_id));
        assert_eq!(
            compiler.environment_stack.fact_names.get(&outer_fact_id),
            Some(&"__fact0".to_string())
        );
        assert!(compiler.declarations[0]
            .contains("∃ (x : ℂ), Litex.In x Litex.R ∧ Litex.Same x (1 : ℂ)"));
        assert!(compiler.declarations[0].contains("have __step1"));
        assert!(compiler.declarations[0].contains("⟨(1 : ℂ)"));
    }

    #[test]
    fn existential_witness_rejects_a_missing_parameter_check_child() {
        let mut results = execute_single_existential_witness();
        let result = single_existential_witness_result_mut(&mut results);
        result
            .verification
            .as_mut()
            .expect("witness retains verification")
            .parameter_checks[0] = None;

        let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing parameter child must fail closed");
        assert!(error.contains("has no parameter-check child Result"));
    }

    #[test]
    fn existential_witness_rejects_a_missing_outer_fact_id() {
        let mut results = execute_single_existential_witness();
        let result = single_existential_witness_result_mut(&mut results);
        result.common.infers.store_fact_outputs[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing outer FactId must fail closed");
        assert!(error.contains("existential witness outer effect store has no FactId"));
    }

    #[test]
    fn existential_elimination_uses_source_and_projection_fact_ids_directly() {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
        let [StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessExistFact(witness),
        )), StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::ObtainObjFromExistFact(elimination),
        ))] = results.as_slice()
        else {
            panic!("expected witness followed by existential elimination")
        };
        let source_fact_id = witness.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("witness retains source FactId");
        let source_citation = elimination
            .verification
            .as_ref()
            .expect("elimination retains verification")
            .source_result
            .factual_success()
            .expect("elimination source is factual");
        let SuccessFactProofResult::Fact(source_citation) = source_citation.proof() else {
            panic!("elimination source cites the stored existential")
        };
        assert_eq!(source_citation.source_fact_id, Some(source_fact_id));

        let mut compiler = StmtResultToLeanCompiler::new("direct_existential_elimination.lit");
        assert!(compiler
            .compile_witness_exist_fact_stmt_result_to_lean_source(witness)
            .expect("compile direct existential introduction"));
        assert!(compiler
            .compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(elimination)
            .expect("compile direct existential elimination"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(compiler.declarations[1].contains("noncomputable def y : ℂ := Classical.choose"));
        assert!(compiler.declarations[1].contains("from __fact0"));
        assert!(compiler.declarations[2].contains("Classical.choose_spec"));
        assert!(compiler.declarations[2].contains("from __fact0"));
        assert!(compiler.declarations[2].contains(").1"));
        assert!(compiler.declarations[3].contains("Classical.choose_spec"));
        assert!(compiler.declarations[3].contains("from __fact0"));
        assert!(compiler.declarations[3].contains(").2"));
    }

    #[test]
    fn existential_elimination_rejects_a_projection_without_fact_id() {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
        let StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::ObtainObjFromExistFact(elimination),
        )) = &mut results[1]
        else {
            panic!("expected existential elimination")
        };
        elimination.common.infers.store_fact_outputs[1].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_existential_elimination.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("projection without FactId must fail closed");
        assert!(error.contains("existential elimination projections store 1"));
    }

    fn execute_predicate_backed_existential_elimination() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop has_copy(a R):\n    exist x R st {x = a}\nwitness exist x R st {x = 2} from 2:\n    2 = 2\nby def $has_copy(2)\nobtain copy from $has_copy(2)\n",
            "direct_predicate_backed_existential_elimination.lit",
        )
        .expect("execute predicate-backed existential elimination")
    }

    #[test]
    fn predicate_backed_existential_elimination_compiles_definition_projection_directly() {
        let results = execute_predicate_backed_existential_elimination();
        let [definition, witness, by_definition, StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::ObtainObjFromAtomicFact(elimination),
        ))] = results.as_slice()
        else {
            panic!("expected predicate definition, witness, by-definition, and obtain")
        };

        let mut compiler =
            StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
        for result in [definition, witness, by_definition] {
            compiler
                .compile_stmt_result_to_lean_source(result)
                .expect("compile prerequisite Result directly");
        }
        assert!(compiler
            .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(elimination)
            .expect("compile predicate-backed elimination directly"));
        assert!(compiler
            .declarations
            .iter()
            .any(|declaration| declaration.contains("unfold has_copy at __definition")));
        assert!(compiler
            .declarations
            .iter()
            .any(|declaration| declaration.contains("noncomputable def copy")));
    }

    #[test]
    fn predicate_backed_existential_elimination_rejects_an_unpublished_source_fact_id() {
        let mut results = execute_predicate_backed_existential_elimination();
        let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(
            by_definition,
        ))) = &mut results[2]
        else {
            panic!("expected by-definition prerequisite")
        };
        let source_fact_id = by_definition.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("by-definition retains source FactId");
        by_definition.common.infers.store_fact_outputs[0].fact_id =
            Some(FactId::new(source_fact_id.value() + 10_000));

        let mut compiler =
            StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
        for result in &results[..3] {
            compiler
                .compile_stmt_result_to_lean_source(result)
                .expect("compile corrupted prerequisites up to the changed publication identity");
        }
        let StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::ObtainObjFromAtomicFact(elimination),
        )) = &results[3]
        else {
            panic!("expected predicate-backed elimination")
        };
        let error = compiler
            .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(elimination)
            .expect_err("unpublished cited FactId must fail closed");
        assert!(
            error.contains(&format!("unavailable cited fact `{source_fact_id}`")),
            "{error}"
        );
    }

    fn execute_direct_cases_and_contradiction() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "by cases:\n    ? 2 = 2\n    case 1 = 1 and 2 = 2:\n        1 = 1\nby contra:\n    ? not 2 < 1\n    impossible 2 < 1\n",
            "direct_cases_and_contradiction.lit",
        )
        .expect("execute direct cases and contradiction")
    }

    #[test]
    fn cases_and_contradiction_compile_directly_in_nested_environments() {
        let results = execute_direct_cases_and_contradiction();
        let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))), StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
            contradiction,
        )))] = results.as_slice()
        else {
            panic!("expected cases followed by contradiction")
        };
        let branch = &cases
            .verification
            .as_ref()
            .expect("cases retains verification")
            .branches[0];
        let branch_assumption_fact_id = branch.assumption_fact_id;
        let branch_component_fact_ids = branch
            .proof_scope
            .assumption_components
            .iter()
            .map(|(fact_id, _)| *fact_id)
            .collect::<Vec<_>>();
        let reverse_assumption_fact_id = contradiction
            .verification
            .as_ref()
            .expect("contra retains verification")
            .reverse_assumption_fact_id;

        let mut compiler = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit");
        let coverage = cases
            .verification
            .as_ref()
            .expect("cases retains verification")
            .coverage_check
            .factual_success()
            .expect("coverage is factual");
        assert!(
            compiler
                .construct_lean_proof_from_direct_fact_result(coverage)
                .expect("construct coverage proof")
                .is_some(),
            "coverage proof remained unsupported: {:?}",
            coverage.proof()
        );
        assert!(compiler
            .compile_by_cases_stmt_result_to_lean_source(cases)
            .expect("compile cases directly"));
        assert!(compiler
            .compile_by_contra_stmt_result_to_lean_source(contradiction)
            .expect("compile contradiction directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&branch_assumption_fact_id));
        assert!(branch_component_fact_ids
            .iter()
            .all(|fact_id| !compiler.environment_stack.fact_names.contains_key(fact_id)));
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&reverse_assumption_fact_id));
        assert!(compiler.declarations[0].contains("have __case1_component1"));
        assert!(compiler.declarations[0].contains("have __case1_component2"));
        assert!(compiler.declarations[1].contains("Classical.byContradiction"));
    }

    #[test]
    fn cases_and_contradiction_tracer_compiles_from_recursive_results() {
        let source = include_str!("../../lean/examples/9_CasesAndContradiction.lit");
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            source,
            "9_CasesAndContradiction.lit",
        )
        .expect("execute cases-and-contradiction tracer");
        let lean_source = StmtResultToLeanCompiler::new("9_CasesAndContradiction.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile recursive cases-and-contradiction Results");
        assert!(lean_source.contains("__case1_component1"));
        assert!(lean_source.contains("Classical.byContradiction"));
    }

    #[test]
    fn cases_reject_a_branch_assumption_fact_id_mismatch() {
        let mut results = execute_direct_cases_and_contradiction();
        let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))) =
            &mut results[0]
        else {
            panic!("expected cases result")
        };
        let exported_fact_id = cases.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("cases exports a FactId");
        cases
            .verification
            .as_mut()
            .expect("cases retains verification")
            .branches[0]
            .assumption_fact_id = exported_fact_id;

        let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("mismatched branch FactId must fail closed");
        assert!(error.contains("branch assumption FactIds disagree"));
    }

    #[test]
    fn contradiction_rejects_a_reverse_assumption_fact_id_mismatch() {
        let mut results = execute_direct_cases_and_contradiction();
        let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
            contradiction,
        ))) = &mut results[1]
        else {
            panic!("expected contradiction result")
        };
        let exported_fact_id = contradiction.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("contradiction exports a FactId");
        contradiction
            .verification
            .as_mut()
            .expect("contradiction retains verification")
            .reverse_assumption_fact_id = exported_fact_id;

        let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("mismatched reverse FactId must fail closed");
        assert!(error.contains("reverse-assumption FactIds disagree"));
    }

    fn execute_ordinary_claim() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "claim:\n    ? 2 = 2\n    2 = 2\n",
            "direct_claim.lit",
        )
        .expect("execute ordinary claim")
    }

    fn ordinary_claim_result_mut(results: &mut [StmtResult]) -> &mut SuccessClaimStmtResult {
        let [StmtResult::Success(SuccessStmtResult::ProofBlock(
            SuccessProofBlockStmtResult::ClaimStmt(result),
        ))] = results
        else {
            panic!("expected one successful claim result")
        };
        result
    }

    #[test]
    fn local_claim_proof_step_store_keeps_its_local_fact_id_after_outer_store() {
        let mut results = execute_ordinary_claim();
        let claim = ordinary_claim_result_mut(&mut results);
        let outer_fact_id = claim.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("claim outer store has a FactId");
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &claim.verification else {
            panic!("ordinary claim retains ordinary-fact verification")
        };
        let local = verification.proof_steps[0]
            .factual_success()
            .expect("claim proof step is factual");
        let local_fact_id = local
            .store
            .fact_id
            .expect("local proof step has a frozen FactId");

        assert_ne!(local_fact_id, outer_fact_id);
        assert_eq!(
            local.store.infers.store_fact_outputs[0].fact_id,
            Some(local_fact_id)
        );
        let SuccessFactProofResult::Fact(citation) = verification
            .conclusion_check
            .factual_success()
            .expect("claim conclusion is factual")
            .proof()
        else {
            panic!("claim conclusion cites its local proof step")
        };
        assert_eq!(citation.source_fact_id, Some(local_fact_id));
    }

    #[test]
    fn ordinary_claim_and_example_compile_directly_from_recursive_results() {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "claim:\n    ? 2 = 2\n    2 = 2\n\nexample:\n    ? 3 = 3\n    3 = 3\n",
            "direct_claim_and_example.lit",
        )
        .expect("execute claim and example");
        let [StmtResult::Success(SuccessStmtResult::ProofBlock(
            SuccessProofBlockStmtResult::ClaimStmt(claim),
        )), StmtResult::Success(SuccessStmtResult::ProofBlock(
            SuccessProofBlockStmtResult::ExampleStmt(example),
        ))] = results.as_slice()
        else {
            panic!("expected claim and example results")
        };

        let mut compiler = StmtResultToLeanCompiler::new("direct_claim_and_example.lit");
        assert!(compiler
            .compile_claim_stmt_result_to_lean_source(claim)
            .expect("direct claim compilation succeeds"));
        assert!(compiler
            .compile_example_stmt_result_to_lean_source(example)
            .expect("direct example compilation succeeds"));
        assert!(compiler.declarations[0].contains("theorem __fact0"));
        assert!(compiler.declarations[0].contains("have __step1"));
        assert!(compiler.declarations[0].contains("exact __step1"));
        assert!(compiler.declarations[1].starts_with("example :"));
        assert!(compiler.declarations[1].contains("have __step1"));
    }

    #[test]
    fn direct_claim_compiler_rejects_a_local_store_retargeted_to_the_outer_fact_id() {
        let mut results = execute_ordinary_claim();
        let claim = ordinary_claim_result_mut(&mut results);
        let outer_fact_id = claim.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("claim outer store has a FactId");
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &mut claim.verification else {
            panic!("ordinary claim retains ordinary-fact verification")
        };
        verification.proof_steps[0]
            .factual_success_mut()
            .expect("claim proof step is factual")
            .store
            .infers
            .store_fact_outputs[0]
            .fact_id = Some(outer_fact_id);

        let error = StmtResultToLeanCompiler::new("direct_claim.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("retargeted local store must fail closed");
        assert!(error.contains("local proof-step store does not retain its exact FactId"));
    }

    fn execute_zero_binder_named_theorem() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm one_eq_one:\n    ? forall:\n        1 = 1\n",
            "direct_zero_binder_theorem.lit",
        )
        .expect("execute zero-binder named theorem")
    }

    fn named_theorem_result_mut(results: &mut [StmtResult]) -> &mut SuccessDefThmStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefThmStmt(result))] = results else {
            panic!("expected one successful named-theorem result")
        };
        result
    }

    #[test]
    fn zero_binder_named_theorem_compiles_directly_from_recursive_result() {
        let mut results = execute_zero_binder_named_theorem();
        let theorem = named_theorem_result_mut(&mut results);
        let mut compiler = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit");

        assert!(compiler
            .compile_named_theorem_stmt_result_to_lean_source(theorem)
            .expect("direct zero-binder theorem compilation succeeds"));
        assert_eq!(compiler.declarations.len(), 1);
        assert!(compiler.declarations[0].starts_with("theorem one_eq_one :"));
        assert!(compiler.declarations[0].contains("have __c0_0"));
        assert!(compiler.declarations[0].contains("exact __c0_0"));
    }

    #[test]
    fn zero_binder_named_theorem_compiler_ignores_conclusion_diagnostic_label() {
        let original = execute_zero_binder_named_theorem();
        let original_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
            .compile_stmt_results_to_lean_source(&original)
            .expect("compile original zero-binder theorem");

        let mut renamed = execute_zero_binder_named_theorem();
        let theorem = named_theorem_result_mut(&mut renamed);
        let conclusion = theorem
            .verification
            .as_mut()
            .expect("named theorem retains verification")
            .conclusion_checks[0]
            .factual_success_mut()
            .expect("named theorem conclusion is factual");
        let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
            .expect("test conclusion has one proof owner");
        let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
            panic!("expected builtin conclusion proof")
        };
        proof.msg = "diagnostic-only theorem conclusion label".into();

        let renamed_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
            .compile_stmt_results_to_lean_source(&renamed)
            .expect("compile theorem after diagnostic-only mutation");
        assert_eq!(renamed_lean, original_lean);
    }

    #[test]
    fn zero_binder_named_theorem_compiler_rejects_missing_outer_fact_id() {
        let mut results = execute_zero_binder_named_theorem();
        let theorem = named_theorem_result_mut(&mut results);
        theorem.common.infers.store_fact_outputs[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("theorem without its frozen outer FactId must fail closed");
        assert!(error.contains("named theorem outer store has no FactId"));
    }

    #[test]
    fn standard_set_binder_named_theorem_compiles_in_a_child_environment() {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n",
            "direct_binder_theorem.lit",
        )
        .expect("execute standard-set binder theorem");
        let theorem = named_theorem_result_mut(&mut results);
        let mut compiler = StmtResultToLeanCompiler::new("direct_binder_theorem.lit");

        assert!(compiler
            .compile_named_theorem_stmt_result_to_lean_source(theorem)
            .expect("direct binder theorem compilation succeeds"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(compiler.declarations[0].contains("∀ (x : ℂ)"));
        assert!(compiler.declarations[0].contains("(__h0_1 : Litex.In x Litex.R)"));
        assert!(compiler.declarations[0].contains("intro x __h0_1"));
        assert!(compiler.declarations[0].contains("have __step1"));
        assert!(compiler.declarations[0].contains("exact __c0_0"));
    }

    #[test]
    fn existential_theorem_compiles_nested_witness_in_two_child_environments() {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm member_has_witness:\n    ? forall S set, a S:\n        exist x S st {x = a}\n    witness exist x S st {x = a} from a:\n        a = a\n",
            "direct_existential_theorem.lit",
        )
        .expect("execute theorem with a nested existential witness");
        let theorem = named_theorem_result_mut(&mut results);
        let mut compiler = StmtResultToLeanCompiler::new("direct_existential_theorem.lit");

        assert!(compiler
            .compile_named_theorem_stmt_result_to_lean_source(theorem)
            .expect("direct existential theorem compilation succeeds"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 1);
        assert!(compiler.declarations[0].contains("∀ (S : Litex.Set)"));
        assert!(compiler.declarations[0].contains("{__carrier0_2 : Type}"));
        assert!(compiler.declarations[0].contains("(a : __carrier0_2)"));
        assert!(compiler.declarations[0].contains("have __step1 : ∃"));
        assert!(compiler.declarations[0].contains("have __step1 : Litex.Same a a"));
        assert!(compiler.declarations[0].contains("⟨_, a, (__h0_2), (__step1)⟩"));
        assert!(compiler.declarations[0].contains("exact __c0_0"));
    }

    fn execute_named_theorem_and_instantiation() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n\nby thm local_reflexivity(1)\n",
            "direct_theorem_instantiation.lit",
        )
        .expect("execute named theorem and its instantiation")
    }

    fn theorem_instantiation_result_mut(results: &mut [StmtResult]) -> &mut SuccessByThmStmtResult {
        let [_, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(result)))] =
            results
        else {
            panic!("expected a named theorem followed by by-thm")
        };
        result
    }

    #[test]
    fn by_thm_uses_the_exact_source_fact_id_and_argument_check_result() {
        let results = execute_named_theorem_and_instantiation();
        let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(by_theorem))) =
            &results[1]
        else {
            panic!("second Result is by-thm")
        };
        let source_fact_id = by_theorem
            .verification
            .as_ref()
            .expect("by-thm retains verification")
            .source_fact_id
            .expect("by-thm retains its source theorem FactId");
        let json = crate::output::display_stmt_result_json_v2(&results[1]);
        assert!(json.contains(&format!("\"source_fact_id\": \"{source_fact_id}\"")));

        let lean = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile theorem and exact-FactId instantiation");

        assert!(lean.contains("theorem local_reflexivity :"));
        assert!(lean.contains("theorem __fact1 : Litex.Same (1 : ℂ) (1 : ℂ)"));
        assert!(lean.contains("local_reflexivity (1 : ℂ)"));
        assert!(lean.contains("Litex.Rules.complexRealInR (1 : ℝ)"));
    }

    #[test]
    fn by_thm_rejects_a_missing_source_theorem_fact_id() {
        let mut results = execute_named_theorem_and_instantiation();
        theorem_instantiation_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("by-thm retains verification")
            .source_fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("by-thm without its source FactId must fail closed");
        assert!(error.contains("by-thm Result has no source theorem FactId"));
    }

    #[test]
    fn theorem_backed_obtain_consumes_but_does_not_publish_its_local_conclusion() {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}\n    witness exist x R st {x = a} from a:\n        a = a\nobtain selected from thm self_exists(3)\n",
            "direct_theorem_backed_obtain.lit",
        )
        .expect("execute theorem-backed obtain");
        let [StmtResult::Success(SuccessStmtResult::DefThmStmt(theorem)), StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::ObtainObjFromThm(obtain),
        ))] = results.as_slice()
        else {
            panic!("expected theorem followed by theorem-backed obtain")
        };
        let source = obtain
            .verification
            .as_ref()
            .expect("obtain retains elimination verification")
            .source_result
            .non_factual_success()
            .expect("obtain source is a statement Result");
        let SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(application)) = source else {
            panic!("obtain source is a by-thm Result")
        };
        assert_eq!(
            application.common.infers.store_fact_outputs[0].fact_id, None,
            "the temporary theorem conclusion is not publishable after its local environment pops"
        );
        let theorem_fact_id = theorem.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("named theorem retains its published FactId");
        let projection_fact_ids = obtain
            .common
            .infers
            .store_fact_outputs
            .iter()
            .map(|output| output.fact_id.expect("projection retains FactId"))
            .collect::<Vec<_>>();

        let mut compiler = StmtResultToLeanCompiler::new("direct_theorem_backed_obtain.lit");
        assert!(compiler
            .compile_named_theorem_stmt_result_to_lean_source(theorem)
            .expect("compile source theorem"));
        assert!(compiler
            .compile_obtain_obj_from_theorem_stmt_result_to_lean_source(obtain)
            .expect("compile theorem-backed obtain"));
        assert_eq!(compiler.environment_stack.fact_names.len(), 3);
        assert!(compiler
            .environment_stack
            .fact_names
            .contains_key(&theorem_fact_id));
        for fact_id in projection_fact_ids {
            assert!(compiler.environment_stack.fact_names.contains_key(&fact_id));
        }
        assert_eq!(compiler.declarations.len(), 4);
        assert!(compiler.declarations[1].contains("noncomputable def selected"));
    }

    fn execute_concrete_predicate_and_by_definition() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
            "direct_by_definition.lit",
        )
        .expect("execute concrete predicate and by-definition")
    }

    fn by_definition_result_mut(results: &mut [StmtResult]) -> &mut SuccessByDefStmtResult {
        let [_, _, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(result)))] =
            results
        else {
            panic!("expected concrete predicate, fact, and by-definition Results")
        };
        result
    }

    #[test]
    fn by_definition_combines_parameter_and_clause_results_directly() {
        let results = execute_concrete_predicate_and_by_definition();
        let mut compiler = StmtResultToLeanCompiler::new("direct_by_definition.lit");
        let StmtResult::Success(SuccessStmtResult::DefPredicateStmt(
            SuccessDefPredicateStmtResult::DefPropStmt(definition),
        )) = &results[0]
        else {
            panic!("first Result is a concrete predicate definition")
        };
        let StmtResult::Success(SuccessStmtResult::Fact(fact)) = &results[1] else {
            panic!("second Result is the reusable clause fact")
        };
        let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(
            by_definition,
        ))) = &results[2]
        else {
            panic!("third Result is by-definition")
        };

        compiler
            .compile_def_prop_stmt_result_to_lean_source(definition)
            .expect("compile concrete predicate directly");
        compiler
            .compile_fact_stmt_result_to_lean_source(fact)
            .expect("compile reusable clause fact directly");
        assert!(compiler
            .compile_by_definition_stmt_result_to_lean_source(by_definition)
            .expect("compile by-definition directly"));
        assert!(compiler.declarations[2].contains("unfold is_unit_pair"));
        assert!(compiler.declarations[2].contains(
            "exact ⟨Litex.Rules.complexRealInR (1 : ℝ), Litex.Rules.complexRealInR (1 : ℝ), __fact0, __fact0⟩"
        ));
    }

    #[test]
    fn by_definition_rejects_a_missing_clause_child_result() {
        let mut results = execute_concrete_predicate_and_by_definition();
        by_definition_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("by-definition retains verification")
            .clause_checks
            .pop();

        let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing clause child must fail closed");
        assert!(error.contains("changed its component arity"));
    }

    #[test]
    fn by_definition_rejects_a_missing_target_fact_id() {
        let mut results = execute_concrete_predicate_and_by_definition();
        by_definition_result_mut(&mut results)
            .common
            .infers
            .store_fact_outputs[0]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("by-definition target without FactId must fail closed");
        assert!(error.contains("by-definition target store has no FactId"));
    }

    fn execute_named_real_function(source: &str) -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            source,
            "direct_named_real_function.lit",
        )
        .expect("execute named real function")
    }

    fn named_real_function_result_mut(
        results: &mut [StmtResult],
    ) -> &mut SuccessHaveFnEqualStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveFnEqualStmt(result),
        ))] = results
        else {
            panic!("expected one named-function Result")
        };
        result
    }

    #[test]
    fn named_real_function_compiles_return_check_in_child_environment() {
        let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
        let result = named_real_function_result_mut(&mut results);
        let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
            .fact_id
            .expect("defining equality retains FactId");
        let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

        assert!(compiler
            .compile_have_fn_equal_stmt_result_to_lean_source(result)
            .expect("compile named real function directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 3);
        assert!(compiler.declarations[0].contains("noncomputable def inc : Litex.Fn"));
        assert!(compiler.declarations[0].contains("Litex.In.rep __arg __arg_in + (1 : ℝ)"));
        let binding = compiler
            .environment_stack
            .named_function_definitions
            .get(&defining_equality_fact_id)
            .expect("direct function publishes its reduction binding");
        assert!(binding.uses_native_real_body);
        assert!(binding.compatibility_return_selection.is_none());
    }

    #[test]
    fn named_real_function_domain_fact_stays_inside_function_binder() {
        let mut results =
            execute_named_real_function("have fn reciprocal(x R: x != 0) R = 1 / x\n");
        let result = named_real_function_result_mut(&mut results);
        let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

        assert!(compiler
            .compile_have_fn_equal_stmt_result_to_lean_source(result)
            .expect("compile domain-constrained real function directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(compiler.declarations[0].contains("Litex.FnWhere"));
        assert!(compiler.declarations[0].contains("__arg_domain"));
        assert!(compiler
            .environment_stack
            .fact_propositions
            .values()
            .all(|fact| fact.to_string() != "x != 0"));
    }

    #[test]
    fn named_real_function_rejects_missing_local_parameter_fact_id() {
        let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
        named_real_function_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("function retains verification")
            .assumption_infers
            .store_fact_outputs[0]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing local parameter FactId must fail closed");
        assert!(error.contains("named real function local assumptions store 0"));
        assert!(error.contains("has no FactId"));
    }

    fn execute_indexed_tuple_definition() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have tuple coordinates for index <= 3, coordinates[index] = index + 1\n",
            "direct_indexed_tuple.lit",
        )
        .expect("execute indexed tuple definition")
    }

    fn indexed_tuple_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveTupleStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveTupleStmt(result),
        ))] = results
        else {
            panic!("expected one indexed tuple Result")
        };
        result
    }

    #[test]
    fn indexed_tuple_compiles_value_well_definedness_in_child_environment() {
        let mut results = execute_indexed_tuple_definition();
        let result = indexed_tuple_result_mut(&mut results);
        let verification = result
            .verification
            .as_ref()
            .expect("indexed tuple retains combined verification");
        match verification.value_well_definedness.as_ref() {
            SuccessVerifyObjWellDefinedResult::Direct(value) => {
                assert_eq!(
                    obj_equality_key(&value.object),
                    obj_equality_key(&result.statement.value)
                );
            }
            other => panic!("expected direct tuple value WD Result, found {other:?}"),
        }
        let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit");

        assert!(compiler
            .compile_have_tuple_stmt_result_to_lean_source(result)
            .expect("compile indexed tuple directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 6);
        assert!(compiler.declarations[2]
            .contains("noncomputable def coordinates : Litex.IndexedTuple 3 ℂ"));
        assert!(compiler.declarations[2].contains("__index.val"));
        assert!(compiler.declarations[2].contains("+ (1 : ℂ)"));
        assert!(compiler.declarations[5].contains("∀ {__tuple_index_carrier : Type}"));
        assert!(!compiler
            .environment_stack
            .symbol_names
            .contains_key(&result.statement.index_binding.id()));
    }

    #[test]
    fn indexed_tuple_rejects_a_coordinate_store_without_fact_id() {
        let mut results = execute_indexed_tuple_definition();
        indexed_tuple_result_mut(&mut results)
            .common
            .infers
            .store_fact_outputs[2]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("coordinate store without a FactId must fail closed");
        assert!(error.contains("lost its FactId"));
    }

    fn execute_indexed_sequence_definition() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have seq identity_sequence seq(R) for index, identity_sequence(index) = index + 1\n",
            "direct_indexed_sequence.lit",
        )
        .expect("execute indexed sequence definition")
    }

    fn indexed_sequence_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveSeqStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveSeqStmt(result),
        ))] = results
        else {
            panic!("expected one indexed sequence Result")
        };
        result
    }

    #[test]
    fn indexed_sequence_compiles_return_check_in_its_index_environment() {
        let mut results = execute_indexed_sequence_definition();
        let result = indexed_sequence_result_mut(&mut results);
        let verification = result
            .verification
            .as_ref()
            .expect("sequence retains combined verification");
        let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
            .fact_id
            .expect("sequence index membership retains its local FactId");
        let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
            .fact_id
            .expect("sequence equality retains its outer FactId");
        let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit");

        assert!(compiler
            .compile_have_sequence_stmt_result_to_lean_source(result)
            .expect("compile indexed sequence directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 4);
        assert!(compiler.declarations[0]
            .contains("noncomputable def identity_sequence : Litex.Fn Litex.NPos Litex.R"));
        assert!(compiler.declarations[0].contains("(Litex.In.rep __arg __arg_in).val : ℕ"));
        assert!(compiler.declarations[0].contains("+ (1 : ℝ)"));
        assert!(compiler.declarations[1].contains("Litex.sequenceSet Litex.R"));
        assert!(compiler.declarations[2].contains("Litex.fnSet Litex.NPos Litex.R"));
        assert!(!compiler
            .environment_stack
            .symbol_names
            .contains_key(&result.statement.index_binding.id()));
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&parameter_fact_id));
        assert!(compiler
            .environment_stack
            .named_function_definitions
            .contains_key(&defining_equality_fact_id));
    }

    #[test]
    fn indexed_sequence_rejects_a_missing_local_parameter_fact_id() {
        let mut results = execute_indexed_sequence_definition();
        indexed_sequence_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("sequence retains verification")
            .assumption_infers
            .store_fact_outputs[0]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("sequence index without a local FactId must fail closed");
        assert!(error.contains("sequence index parameter store has no FactId"));
    }

    fn execute_finite_sequence_definition() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have finite_seq bounded_sequence finite_seq(R, 3) for index <= 3, bounded_sequence(index) = index + 1\nbounded_sequence(2) = 2 + 1\n",
            "direct_finite_sequence.lit",
        )
        .expect("execute finite-sequence definition and application")
    }

    fn finite_sequence_result_mut(
        results: &mut [StmtResult],
    ) -> &mut SuccessHaveFiniteSeqStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveFiniteSeqStmt(result),
        )), _] = results
        else {
            panic!("expected a finite-sequence definition followed by an application fact")
        };
        result
    }

    #[test]
    fn finite_sequence_compiles_bound_scope_and_application_from_recursive_results() {
        let mut results = execute_finite_sequence_definition();
        let result = finite_sequence_result_mut(&mut results);
        let verification = result
            .verification
            .as_ref()
            .expect("finite sequence retains combined verification");
        assert_eq!(verification.bound_checks.len(), 2);
        assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 2);
        let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
            .fact_id
            .expect("finite-sequence parameter membership retains its local FactId");
        let domain_fact_id = verification.assumption_infers.store_fact_outputs[1]
            .fact_id
            .expect("finite-sequence domain premise retains its local FactId");
        let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
            .fact_id
            .expect("finite-sequence equality retains its outer FactId");
        let mut compiler = StmtResultToLeanCompiler::new("direct_finite_sequence.lit");

        assert!(compiler
            .compile_have_finite_sequence_stmt_result_to_lean_source(result)
            .expect("compile finite sequence directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 4);
        assert!(compiler.declarations[0]
            .contains("noncomputable def bounded_sequence : Litex.FnTelescope.Carrier"));
        assert!(compiler.declarations[0].contains("Litex.FnTelescope.requirement"));
        assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
        assert!(compiler.declarations[1].contains("Litex.finiteSequenceSet.{0} Litex.R (3 : Nat)"));
        assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
        assert!(!compiler
            .environment_stack
            .symbol_names
            .contains_key(&result.statement.index_binding.id()));
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&parameter_fact_id));
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&domain_fact_id));
        assert!(compiler
            .environment_stack
            .named_function_definitions
            .contains_key(&defining_equality_fact_id));
    }

    #[test]
    fn finite_sequence_rejects_a_missing_local_domain_fact_id() {
        let mut results = execute_finite_sequence_definition();
        finite_sequence_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("finite sequence retains verification")
            .assumption_infers
            .store_fact_outputs[1]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_finite_sequence.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("finite-sequence domain without a local FactId must fail closed");
        assert!(error.contains("finite-sequence domain store has no FactId"));
    }

    fn execute_matrix_definition() -> Vec<StmtResult> {
        crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have matrix entry_matrix matrix(R, 2, 3) for row <= 2, column <= 3, entry_matrix(row, column) = row + column\nentry_matrix(2, 3) = 2 + 3\n",
            "direct_matrix.lit",
        )
        .expect("execute matrix definition and application")
    }

    fn matrix_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveMatrixStmtResult {
        let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveMatrixStmt(result),
        )), _] = results
        else {
            panic!("expected a matrix definition followed by an application fact")
        };
        result
    }

    #[test]
    fn matrix_compiles_two_parameter_and_two_domain_results_in_one_child_environment() {
        let mut results = execute_matrix_definition();
        let result = matrix_result_mut(&mut results);
        let verification = result
            .verification
            .as_ref()
            .expect("matrix retains combined verification");
        assert_eq!(verification.bound_checks.len(), 4);
        assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 4);
        let local_fact_ids = verification
            .assumption_infers
            .store_fact_outputs
            .iter()
            .map(|store| store.fact_id.expect("matrix local store retains FactId"))
            .collect::<Vec<_>>();
        let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
            .fact_id
            .expect("matrix equality retains its outer FactId");
        let mut compiler = StmtResultToLeanCompiler::new("direct_matrix.lit");

        assert!(compiler
            .compile_have_matrix_stmt_result_to_lean_source(result)
            .expect("compile matrix directly"));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert_eq!(compiler.declarations.len(), 4);
        assert!(compiler.declarations[0]
            .contains("noncomputable def entry_matrix : Litex.FnTelescope.Carrier"));
        assert!(compiler.declarations[0].contains("__arg1"));
        assert!(compiler.declarations[0].contains("__arg2"));
        assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
        assert!(
            compiler.declarations[1].contains("Litex.matrixSet.{0} Litex.R (2 : Nat) (3 : Nat)")
        );
        assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
        for fact_id in local_fact_ids {
            assert!(!compiler.environment_stack.fact_names.contains_key(&fact_id));
        }
        assert!(!compiler
            .environment_stack
            .symbol_names
            .contains_key(&result.statement.row_index_binding.id()));
        assert!(!compiler
            .environment_stack
            .symbol_names
            .contains_key(&result.statement.col_index_binding.id()));
        assert!(compiler
            .environment_stack
            .named_function_definitions
            .contains_key(&defining_equality_fact_id));
    }

    #[test]
    fn matrix_rejects_a_missing_local_column_domain_fact_id() {
        let mut results = execute_matrix_definition();
        matrix_result_mut(&mut results)
            .verification
            .as_mut()
            .expect("matrix retains verification")
            .assumption_infers
            .store_fact_outputs[3]
            .fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_matrix.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("matrix column domain without a local FactId must fail closed");
        assert!(error.contains("matrix domain store 1 has no FactId"));
    }

    #[test]
    fn registered_set_rule_rejects_stale_fingerprint() {
        let rule = crate::litex_to_lean_ir::LitexToLeanRegisteredRuleApplicationIr {
            rule_id: RuleId::new(SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID)
                .expect("valid stable rule id"),
            semantic_fingerprint: RuleFingerprint::from_hex("0".repeat(64))
                .expect("valid forged fingerprint shape"),
            bindings: Vec::new(),
        };
        assert!(registered_set_rule(&rule).is_none());
    }
}
