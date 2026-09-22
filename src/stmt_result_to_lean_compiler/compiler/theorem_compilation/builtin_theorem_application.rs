//! Builtin theorem application dispatch.

use super::super::*;
use super::real_analysis_builtins::builtin_theorem_requirement_roles;

impl StmtResultToLeanCompiler {
    /// Compile a reserved builtin theorem only from its typed identity and
    /// retained requirement child.  Most builtin theorem interfaces are an
    /// explicit name for a proof route that already returned the exact
    /// conclusion as a factual child Result; replay that child directly rather
    /// than rediscovering the fact from its spelling.
    pub(in super::super) fn compile_builtin_theorem_application_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &verification.source
        else {
            return Ok(false);
        };
        if matches!(
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
            return self.compile_real_analysis_builtin_theorem_application(result);
        }
        if source.conclusion_well_definedness.is_some() {
            return Err(
                "ordinary builtin theorem unexpectedly retained dedicated conclusion WD evidence"
                    .into(),
            );
        }
        if verification.theorem != source.theorem_id.as_str()
            || verification.theorem != result.statement.name().to_string()
            || verification.arguments.len() != result.statement.args().len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args().iter())
                .any(|(retained, source)| obj_equality_key(retained) != obj_equality_key(source))
        {
            return Err("builtin theorem Result changed its identity or argument order".into());
        }
        let expected_roles = builtin_theorem_requirement_roles(source.theorem_id);
        if source.requirement_roles != expected_roles
            || source.requirement_facts.len() != source.requirement_roles.len()
            || source.requirement_checks.len() != source.requirement_roles.len()
        {
            return Err("builtin theorem Result changed its typed requirement schema".into());
        }
        let expected_provenance = match source.theorem_id {
            BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily
            | BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise => {
                Some(BuiltinTheoremProvenance::AxiomOfChoice)
            }
            _ => None,
        };
        if source.provenance != expected_provenance {
            return Err("builtin theorem Result changed its typed provenance".into());
        }
        let [conclusion] = verification.direct_conclusions.as_slice() else {
            return Err("builtin theorem Result must retain exactly one direct conclusion".into());
        };

        // These three interfaces need dedicated target theorems rather than a
        // conclusion-shaped child.  They remain fail-closed until those exact
        // ABI lemmas are installed below this shared typed entry point.
        if let Some(limitation) = match source.theorem_id {
            BuiltinTheoremId::SubsetOfFiniteSetIsFinite => Some(
                "builtin theorem `subset_of_finite_set_is_finite` requires an exact finite-subcarrier transport theorem for Litex.Set",
            ),
            BuiltinTheoremId::FiniteSetHasBijectiveIndex => Some(
                "builtin theorem `finite_set_has_bijective_index` requires an exact finite-carrier enumeration and bijection target ABI",
            ),
            BuiltinTheoremId::RationalHasUniqueReducedFraction => Some(
                "builtin theorem `rational_has_unique_reduced_fraction` requires a reviewed bridge from heterogeneous Litex.Same to the native rational normal form",
            ),
            _ => None,
        } {
            return Err(limitation.into());
        }

        let [requirement_fact] = source.requirement_facts.as_slice() else {
            return Err(
                "builtin theorem direct adapter requires one retained requirement fact".into(),
            );
        };
        let [requirement_check] = source.requirement_checks.as_slice() else {
            return Err(
                "builtin theorem direct adapter requires one retained requirement child".into(),
            );
        };
        if requirement_fact.to_string() != conclusion.to_string() {
            return Err("builtin theorem direct adapter requirement changed its conclusion".into());
        }
        let requirement_check = requirement_check
            .verified()
            .ok_or_else(|| "builtin theorem requirement child is not factual".to_string())?;
        validate_scoped_fact_check_result(
            requirement_check,
            conclusion,
            "builtin theorem requirement child",
        )?;
        let [outer_store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("builtin theorem must retain exactly one outer conclusion store".into());
        };
        let checked_fact_id = outer_store
            .fact_id
            .ok_or_else(|| "builtin theorem conclusion store has no FactId".to_string())?;
        if outer_store.itself_and_why_itself_is_stored.0.to_string() != conclusion.to_string()
            || outer_store.inferred_facts.len() != outer_store.inferred_fact_ids.len()
        {
            return Err(
                "builtin theorem outer publication changed the checked conclusion's root fact, FactId, or inferred child arity"
                    .into(),
            );
        }
        let Some(proof) = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                requirement_check,
            )?
        else {
            return Err(format!(
                "builtin theorem `{}` checked conclusion has no direct typed proof consumer",
                source.theorem_id
            ));
        };
        let proposition =
            self.render_fact_using_well_definedness_result(&requirement_check.checked, conclusion)?;
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(checked_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(checked_fact_id, conclusion.clone());
        self.next_fact_name_index += 1;

        if result.common.infers.rule_applications.is_empty()
            && outer_store.inferred_facts.is_empty()
            && outer_store.inferred_fact_ids.is_empty()
        {
            return Ok(true);
        }
        if source.theorem_id == BuiltinTheoremId::SetBuilderMember {
            self.compile_set_builder_membership_infer_result_as_top_level_declarations(
                conclusion,
                checked_fact_id,
                &source_name,
                &result.common.infers,
            )?;
        } else if source.theorem_id == BuiltinTheoremId::CartesianMemberFromCoordinates {
            self.compile_literal_cartesian_membership_infer_result_as_top_level_declarations(
                requirement_check,
                conclusion,
                checked_fact_id,
                &result.common.infers,
            )?;
        } else {
            self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
                &result.common.infers,
                &[(checked_fact_id, conclusion.clone())],
                &format!("builtin theorem `{}` outer inference", source.theorem_id),
            )?;
        }
        Ok(true)
    }
}
