//! Empty-set equality from nonemptiness and size evidence.

use crate::prelude::*;

impl Runtime {
    pub(super) fn try_verify_empty_set_equality_from_not_nonempty(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };

        let not_nonempty: AtomicFact =
            NotIsNonemptySetFact::new(set.clone(), line_file.clone()).into();
        let mut sub =
            self.verify_atomic_fact_as_builtin_rule_premise(&not_nonempty, builtin_state)?;
        if !sub.is_success() {
            let empty_order: Option<AtomicFact> = match &set {
                Obj::Range(range) => Some(
                    LessEqualFact::new(
                        range.end.as_ref().clone(),
                        range.start.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into(),
                ),
                Obj::ClosedRange(range) => Some(
                    LessFact::new(
                        range.end.as_ref().clone(),
                        range.start.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into(),
                ),
                _ => None,
            };
            if let Some(empty_order) = empty_order {
                let comparison = self
                    .verify_non_equational_atomic_fact_with_zero_premise_verification(
                        &empty_order,
                    )?;
                if comparison.is_success() {
                    sub = SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        not_nonempty.clone().into(),
                        "integer interval emptiness by number comparison".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyEmptySetEqualityFromNotNonempty01),
                        vec![comparison],
                    )
                    .into();
                }
            }
        }
        if !sub.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                equal_fact.clone().into(),
                SuccessInferResult::new(),
                "empty_set_equality_from_not_nonempty".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyEmptySetEqualityFromNotNonempty02,
                ),
                vec![sub],
            )
            .into(),
        ))
    }

    pub(super) fn try_verify_empty_finite_set_from_size_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let set = match (left, right) {
            (Obj::ListSet(list), set) if list.list.is_empty() => set.clone(),
            (set, Obj::ListSet(list)) if list.list.is_empty() => set.clone(),
            _ => return Ok(None),
        };
        let size: Obj = FiniteSetSize::new(set).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let size_zero = self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
            &size,
            &zero,
            line_file.clone(),
        ));
        if !size_zero.is_success() {
            return Ok(None);
        }

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                equal_fact.clone().into(),
                SuccessInferResult::new(),
                "finite_set_size_zero_implies_empty_set".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyEmptyFiniteSetFromSizeZero,
                ),
                vec![size_zero],
            )
            .into(),
        ))
    }
}
