//! Division and product conversion equalities.

use crate::prelude::*;
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

impl Runtime {
    pub(super) fn literal_zero_obj_for_division_builtin() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    pub(super) fn equal_fact_sides_are_the_same_or_known_equal(
        &self,
        equal_fact: &EqualFact,
    ) -> bool {
        objs_match_for_pattern(&equal_fact.left, &equal_fact.right)
            || self.equal_fact_sides_have_same_known_equality_in_some_env(equal_fact)
    }

    pub(super) fn verify_division_denominator_nonzero_subgoal(
        &mut self,
        denominator: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let not_zero: AtomicFact = NotEqualFact::new(
            denominator.clone(),
            Self::literal_zero_obj_for_division_builtin(),
            line_file,
        )
        .into();
        let result = self.verify_atomic_fact_as_builtin_rule_premise(&not_zero, builtin_state)?;
        if result.is_success() {
            return Ok(Some(result));
        }
        Ok(None)
    }

    pub(super) fn try_verify_product_from_known_division_candidate(
        &mut self,
        equal_fact: &EqualFact,
        dividend: &Obj,
        quotient: &Obj,
        denominator: &Obj,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = &equal_fact.line_file;
        let division_obj: Obj = Div::new(dividend.clone(), denominator.clone()).into();
        if !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            &division_obj,
            quotient,
            line_file.clone(),
        )) {
            return Ok(None);
        }
        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            denominator,
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "division elimination: from a / b = c and b != 0, prove a = c * b".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyProductFromKnownDivisionCandidate,
                ),
                vec![nonzero_result],
            )
            .into(),
        ))
    }

    pub(super) fn try_verify_product_from_known_division(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let (dividend, product) = match (left, right) {
            (dividend, Obj::Mul(product)) => (dividend, product),
            (Obj::Mul(product), dividend) => (dividend, product),
            _ => return Ok(None),
        };

        if let Some(done) = self.try_verify_product_from_known_division_candidate(
            equal_fact,
            dividend,
            product.left.as_ref(),
            product.right.as_ref(),
            builtin_state,
        )? {
            return Ok(Some(done));
        }

        self.try_verify_product_from_known_division_candidate(
            equal_fact,
            dividend,
            product.right.as_ref(),
            product.left.as_ref(),
            builtin_state,
        )
    }

    pub(super) fn try_verify_division_from_known_product(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (division, quotient) = match (left, right) {
            (Obj::Div(division), quotient) => (division, quotient),
            (quotient, Obj::Div(division)) => (division, quotient),
            _ => return Ok(None),
        };

        let product_1: Obj = Mul::new(division.right.as_ref().clone(), quotient.clone()).into();
        let product_2: Obj = Mul::new(quotient.clone(), division.right.as_ref().clone()).into();
        if !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            division.left.as_ref(),
            &product_1,
            line_file.clone(),
        )) && !self.equal_fact_sides_are_the_same_or_known_equal(&EqualFact::new_from_refs(
            division.left.as_ref(),
            &product_2,
            line_file.clone(),
        )) {
            return Ok(None);
        }

        let Some(nonzero_result) = self.verify_division_denominator_nonzero_subgoal(
            division.right.as_ref(),
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "division introduction: from a = b * c and b != 0, prove a / b = c".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyDivisionFromKnownProduct,
                ),
                vec![nonzero_result],
            )
            .into(),
        ))
    }

    // Division can be eliminated into multiplication, and multiplication can be
    // introduced into division when the divisor is nonzero.
    // Example: from `a / b = c`, prove `a = c * b`; from `a = b * c`, prove `a / b = c`.
    pub(super) fn try_verify_division_product_conversion(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_product_from_known_division(equal_fact, builtin_state)?
        {
            return Ok(Some(done));
        }

        self.try_verify_division_from_known_product(equal_fact, builtin_state)
    }
}
