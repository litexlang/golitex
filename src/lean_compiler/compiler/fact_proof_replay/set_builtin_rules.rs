//! Set builtin proof replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_set_builtin_from_result(
        &mut self,
        target: &Fact,
        rule: SetBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let compilation_kind = match rule {
            SetBuiltinRule::EmptySubset => LeanSetBuiltinCompilationKind::EmptySubset,
            SetBuiltinRule::SubsetUnionLeft => LeanSetBuiltinCompilationKind::SubsetUnionLeft,
            SetBuiltinRule::SubsetUnionRight => LeanSetBuiltinCompilationKind::SubsetUnionRight,
            SetBuiltinRule::UnionCommutative => LeanSetBuiltinCompilationKind::UnionCommutative,
            SetBuiltinRule::UnionAssociative => LeanSetBuiltinCompilationKind::UnionAssociative,
            SetBuiltinRule::UnionIdempotent => LeanSetBuiltinCompilationKind::UnionIdempotent,
            SetBuiltinRule::UnionEmptyLeft | SetBuiltinRule::UnionEmptyRight => {
                LeanSetBuiltinCompilationKind::UnionEmptyIdentity
            }
            SetBuiltinRule::UnionSetMinusDecomposition => {
                LeanSetBuiltinCompilationKind::UnionSetMinusDecomposition
            }
            SetBuiltinRule::UnionEqRightOfSubset => {
                LeanSetBuiltinCompilationKind::UnionAbsorptionFromSubset
            }
            SetBuiltinRule::UnionFinite => LeanSetBuiltinCompilationKind::UnionFinite,
            SetBuiltinRule::UnionNonemptyLeft => LeanSetBuiltinCompilationKind::UnionNonemptyLeft,
            SetBuiltinRule::UnionNonemptyRight => LeanSetBuiltinCompilationKind::UnionNonemptyRight,
            SetBuiltinRule::UnionSubset => LeanSetBuiltinCompilationKind::UnionSubset,
            SetBuiltinRule::IntersectCommutative => {
                LeanSetBuiltinCompilationKind::IntersectCommutative
            }
            SetBuiltinRule::IntersectAssociative => {
                LeanSetBuiltinCompilationKind::IntersectAssociative
            }
            SetBuiltinRule::IntersectIdempotent => {
                LeanSetBuiltinCompilationKind::IntersectIdempotent
            }
            SetBuiltinRule::IntersectEqLeftOfSubset => {
                LeanSetBuiltinCompilationKind::IntersectEqLeftOfSubset
            }
            SetBuiltinRule::IntersectEqRightOfSubset => {
                LeanSetBuiltinCompilationKind::IntersectEqRightOfSubset
            }
            SetBuiltinRule::IntersectFinite => LeanSetBuiltinCompilationKind::IntersectFinite,
            SetBuiltinRule::IntersectSubsetLeft => {
                LeanSetBuiltinCompilationKind::IntersectSubsetLeft
            }
            SetBuiltinRule::IntersectSubsetRight => {
                LeanSetBuiltinCompilationKind::IntersectSubsetRight
            }
            SetBuiltinRule::IntersectUnionDistributive => {
                LeanSetBuiltinCompilationKind::IntersectUnionDistributive
            }
            SetBuiltinRule::IntersectSetMinusSelfEmpty => {
                LeanSetBuiltinCompilationKind::IntersectSetMinusSelfEmpty
            }
            SetBuiltinRule::IntersectSetMinusDisjointFromSubset => {
                LeanSetBuiltinCompilationKind::IntersectSetMinusDisjointFromSubset
            }
            SetBuiltinRule::PowerSetFinite => LeanSetBuiltinCompilationKind::PowerSetFinite,
            SetBuiltinRule::PowerSetMembershipOfSubset => {
                LeanSetBuiltinCompilationKind::PowerSetMembershipOfSubset
            }
            SetBuiltinRule::PowerSetNonempty => LeanSetBuiltinCompilationKind::PowerSetNonempty,
            SetBuiltinRule::SetMinusSelfEmpty => LeanSetBuiltinCompilationKind::SetMinusSelfEmpty,
            SetBuiltinRule::SetMinusEmptyRight => LeanSetBuiltinCompilationKind::SetMinusEmptyRight,
            SetBuiltinRule::SetMinusEmptyLeft => LeanSetBuiltinCompilationKind::SetMinusEmptyLeft,
            SetBuiltinRule::SetMinusFiniteLeft => LeanSetBuiltinCompilationKind::SetMinusFiniteLeft,
            SetBuiltinRule::SetMinusInfiniteOfInfiniteFinite => {
                return Err(format!(
                    "builtin rule `{}` has no reviewed ToLean mapping because the Lean ABI does not yet represent infinite-set facts",
                    rule.rule_id()
                ));
            }
            SetBuiltinRule::SetMinusIntersectDeMorgan => {
                LeanSetBuiltinCompilationKind::SetMinusIntersectDeMorgan
            }
            SetBuiltinRule::SetMinusIntersectSelf => {
                LeanSetBuiltinCompilationKind::SetMinusIntersectSelf
            }
            SetBuiltinRule::SetMinusRecoverSubset => {
                LeanSetBuiltinCompilationKind::SetMinusRecoverSubset
            }
            SetBuiltinRule::SetMinusSubsetLeft => LeanSetBuiltinCompilationKind::SetMinusSubsetLeft,
            SetBuiltinRule::SetMinusUnionDeMorgan => {
                LeanSetBuiltinCompilationKind::SetMinusUnionDeMorgan
            }
            SetBuiltinRule::SubsetEqSetMinusRecovery => {
                LeanSetBuiltinCompilationKind::SubsetEqSetMinusRecovery
            }
            SetBuiltinRule::UnionMembershipLeft => {
                LeanSetBuiltinCompilationKind::UnionMembershipLeft
            }
            SetBuiltinRule::UnionMembershipRight => {
                LeanSetBuiltinCompilationKind::UnionMembershipRight
            }
            SetBuiltinRule::IntersectMembershipBoth => {
                LeanSetBuiltinCompilationKind::IntersectMembershipBoth
            }
            SetBuiltinRule::SetMinusMembership => LeanSetBuiltinCompilationKind::SetMinusMembership,
            unsupported => {
                return Err(format!(
                    "builtin rule `{}` has no reviewed ToLean mapping",
                    unsupported.rule_id()
                ));
            }
        };

        if matches!(
            compilation_kind,
            LeanSetBuiltinCompilationKind::UnionCommutative
                | LeanSetBuiltinCompilationKind::UnionAssociative
                | LeanSetBuiltinCompilationKind::UnionIdempotent
                | LeanSetBuiltinCompilationKind::UnionEmptyIdentity
                | LeanSetBuiltinCompilationKind::IntersectCommutative
                | LeanSetBuiltinCompilationKind::IntersectAssociative
        ) {
            if !subgoals.is_empty() {
                return Err("structural set equality unexpectedly gained child Results".into());
            }
            return Ok(Some(render_structural_set_equality(
                target,
                compilation_kind,
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
        if matches!(
            compilation_kind,
            LeanSetBuiltinCompilationKind::UnionMembershipLeft
                | LeanSetBuiltinCompilationKind::UnionMembershipRight
                | LeanSetBuiltinCompilationKind::IntersectMembershipBoth
                | LeanSetBuiltinCompilationKind::SetMinusMembership
        ) {
            return Ok(Some(render_base_set_builtin_rule_from_compiled_children(
                target,
                rule,
                &children,
                &self.environment_stack,
            )?));
        }

        let premises = children
            .into_iter()
            .map(|(fact, proof_expression)| CompiledFactProofBody {
                proposition: String::new(),
                fact,
                proof_expression,
            })
            .collect::<Vec<_>>();
        Ok(Some(render_extended_set_rule(
            target,
            compilation_kind,
            &premises,
            &self.environment_stack,
        )?))
    }
}
