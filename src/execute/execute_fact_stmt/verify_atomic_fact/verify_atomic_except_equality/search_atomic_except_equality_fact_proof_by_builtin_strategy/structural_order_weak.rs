use super::helper::{is_zero_obj, one_obj, two_obj, zero_obj};
use super::result::*;
use crate::ast::fact::{AtomicFact, LessEqualFact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{
    Abs, ArithmeticOperator, FiniteSetMax, FiniteSetMin, FiniteSetStat, Obj, Pow, SetFormer,
    SetOperator, StandardSet,
};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_finite_set_max_list_members_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetMaxListMembersLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(maximum)) = &le.left else {
            return Ok(None);
        };
        let Obj::SetFormer(SetFormer::ListSet(elements)) = maximum.set.as_ref() else {
            return Ok(None);
        };
        if elements.list.is_empty() {
            return Ok(None);
        }
        let mut requirements = Vec::new();
        for element in &elements.list {
            requirements.push(self.strategy_less_equal_fact(
                element.as_ref().clone(),
                le.right.clone(),
                le.line_file.clone(),
            ));
        }

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(FiniteSetMaxListMembersLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_finite_set_max_constructor_parts_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetMaxConstructorPartsLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(maximum)) = &le.left else {
            return Ok(None);
        };
        let Some(parts) = finite_set_constructor_children(maximum.set.as_ref()) else {
            return Ok(None);
        };
        let mut requirements = Vec::new();
        for part in parts {
            requirements.push(self.strategy_is_finite_set_fact(part.clone(), le.line_file.clone()));
            requirements
                .push(self.strategy_is_nonempty_set_fact(part.clone(), le.line_file.clone()));
            requirements.push(self.strategy_less_equal_fact(
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(FiniteSetMax {
                    set: Box::new(part),
                })),
                le.right.clone(),
                le.line_file.clone(),
            ));
        }

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(
            FiniteSetMaxConstructorPartsLessEqualStrategySingleStep {
                requirement_facts,
                proof_of_requirement_facts,
            },
        ))
    }

    pub(super) fn search_finite_set_min_list_members_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetMinListMembersLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(minimum)) = &le.right else {
            return Ok(None);
        };
        let Obj::SetFormer(SetFormer::ListSet(elements)) = minimum.set.as_ref() else {
            return Ok(None);
        };
        if elements.list.is_empty() {
            return Ok(None);
        }
        let mut requirements = Vec::new();
        for element in &elements.list {
            requirements.push(self.strategy_less_equal_fact(
                le.left.clone(),
                element.as_ref().clone(),
                le.line_file.clone(),
            ));
        }

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(FiniteSetMinListMembersLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_finite_set_min_constructor_parts_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetMinConstructorPartsLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(minimum)) = &le.right else {
            return Ok(None);
        };
        let Some(parts) = finite_set_constructor_children(minimum.set.as_ref()) else {
            return Ok(None);
        };
        let mut requirements = Vec::new();
        for part in parts {
            requirements.push(self.strategy_is_finite_set_fact(part.clone(), le.line_file.clone()));
            requirements
                .push(self.strategy_is_nonempty_set_fact(part.clone(), le.line_file.clone()));
            requirements.push(self.strategy_less_equal_fact(
                le.left.clone(),
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(FiniteSetMin {
                    set: Box::new(part),
                })),
                le.line_file.clone(),
            ));
        }

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(
            FiniteSetMinConstructorPartsLessEqualStrategySingleStep {
                requirement_facts,
                proof_of_requirement_facts,
            },
        ))
    }

    pub(super) fn search_product_nonnegative_both_nonneg_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<ProductNonnegativeBothNonnegStrategySingleStep>> {
        let Some((l, r, lf)) = zero_le_mul(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_equal_fact(zero_obj(), r, lf),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(ProductNonnegativeBothNonnegStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_product_nonnegative_both_nonpos_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<ProductNonnegativeBothNonposStrategySingleStep>> {
        let Some((l, r, lf)) = zero_le_mul(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(l, zero_obj(), lf.clone()),
            self.strategy_less_equal_fact(r, zero_obj(), lf),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(ProductNonnegativeBothNonposStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_componentwise_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddComponentwiseLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(left), Some(right)) = (as_add(&le.left), as_add(&le.right)) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(left.0, right.0, le.line_file.clone()),
            self.strategy_less_equal_fact(left.1, right.1, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddComponentwiseLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_crossed_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddCrossedLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(left), Some(right)) = (as_add(&le.left), as_add(&le.right)) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(left.0, right.1, le.line_file.clone()),
            self.strategy_less_equal_fact(left.1, right.0, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddCrossedLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_shared_subtrahend_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SubSharedSubtrahendLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(left), Some(right)) = (as_sub(&le.left), as_sub(&le.right)) else {
            return Ok(None);
        };
        if left.1 != right.1 {
            return Ok(None);
        }
        let requirements =
            vec![self.strategy_less_equal_fact(left.0, right.0, le.line_file.clone())];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(SubSharedSubtrahendLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_shared_minuend_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SubSharedMinuendLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(left), Some(right)) = (as_sub(&le.left), as_sub(&le.right)) else {
            return Ok(None);
        };
        if left.0 != right.0 {
            return Ok(None);
        }
        let requirements =
            vec![self.strategy_less_equal_fact(right.1, left.1, le.line_file.clone())];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(SubSharedMinuendLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_div_shared_positive_denom_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<DivSharedPositiveDenomLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some((left, right, denominator)) =
            super::helper::common_division_parts(&le.left, &le.right)
        else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_fact(zero_obj(), denominator, le.line_file.clone()),
            self.strategy_less_equal_fact(left, right, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(DivSharedPositiveDenomLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_div_shared_negative_denom_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<DivSharedNegativeDenomLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some((left, right, denominator)) =
            super::helper::common_division_parts(&le.left, &le.right)
        else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_fact(denominator, zero_obj(), le.line_file.clone()),
            self.strategy_less_equal_fact(right, left, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(DivSharedNegativeDenomLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_pow_shared_exponent_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<PowSharedExponentLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(left), Some(right)) = (as_pow(&le.left), as_pow(&le.right)) else {
            return Ok(None);
        };
        if left.1 != right.1 {
            return Ok(None);
        }
        let requirements = vec![
            self.strategy_in_fact(
                left.1.clone(),
                Obj::StandardSet(StandardSet::NPos),
                le.line_file.clone(),
            ),
            self.strategy_less_equal_fact(zero_obj(), left.0.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(left.0, right.0, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(PowSharedExponentLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_abs_vs_square_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AbsVsSquareLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(la), Some(ra)) = (as_abs(&le.left), as_abs(&le.right)) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_in_fact(
                la.clone(),
                Obj::StandardSet(StandardSet::R),
                le.line_file.clone(),
            ),
            self.strategy_in_fact(
                ra.clone(),
                Obj::StandardSet(StandardSet::R),
                le.line_file.clone(),
            ),
            self.strategy_less_equal_fact(
                pow_obj(la, two_obj()),
                pow_obj(ra, two_obj()),
                le.line_file.clone(),
            ),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AbsVsSquareLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_nonnegative_shift_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddRightNonnegativeShiftLeftStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(add) = as_add(&le.right) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(le.left.clone(), add.0, le.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), add.1, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightNonnegativeShiftLeftStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_nonnegative_shift_right_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddRightNonnegativeShiftRightStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(add) = as_add(&le.right) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(le.left.clone(), add.1, le.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), add.0, le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightNonnegativeShiftRightStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_left_nonpositive_shift_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddLeftNonpositiveShiftLeftStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(add) = as_add(&le.left) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(add.0, le.right.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(add.1, zero_obj(), le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddLeftNonpositiveShiftLeftStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_left_nonpositive_shift_right_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AddLeftNonpositiveShiftRightStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(add) = as_add(&le.left) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(add.1, le.right.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(add.0, zero_obj(), le.line_file.clone()),
        ];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(AddLeftNonpositiveShiftRightStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_nonpositive_to_zero_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SubNonpositiveToZeroStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        if !is_zero_obj(&le.right) {
            return Ok(None);
        }
        let Some(sub) = as_sub(&le.left) else {
            return Ok(None);
        };
        let requirements = vec![self.strategy_less_equal_fact(sub.0, sub.1, le.line_file.clone())];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(SubNonpositiveToZeroStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_nonnegative_from_zero_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SubNonnegativeFromZeroStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        if !is_zero_obj(&le.left) {
            return Ok(None);
        }
        let Some(sub) = as_sub(&le.right) else {
            return Ok(None);
        };
        let requirements = vec![self.strategy_less_equal_fact(sub.1, sub.0, le.line_file.clone())];

        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(SubNonnegativeFromZeroStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
    pub(super) fn search_mul_scale_factor_one_or_more_right_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<MulScaleFactorOneOrMoreRightStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(product) = as_mul(&le.right) else {
            return Ok(None);
        };
        let mut alts = Vec::new();
        for (factor, scale) in [
            (product.0.clone(), product.1.clone()),
            (product.1.clone(), product.0.clone()),
        ] {
            if factor == le.left {
                alts.push(vec![
                    self.strategy_less_equal_fact(zero_obj(), factor, le.line_file.clone()),
                    self.strategy_less_equal_fact(one_obj(), scale, le.line_file.clone()),
                ]);
            }
        }
        if alts.is_empty() {
            return Ok(None);
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.try_strategy_requirement_alternatives(alts, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(MulScaleFactorOneOrMoreRightStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_mul_scale_factor_one_or_less_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<MulScaleFactorOneOrLessLeftStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let Some(product) = as_mul(&le.left) else {
            return Ok(None);
        };
        let mut alts = Vec::new();
        for (factor, scale) in [
            (product.0.clone(), product.1.clone()),
            (product.1.clone(), product.0.clone()),
        ] {
            if factor == le.right {
                alts.push(vec![
                    self.strategy_less_equal_fact(zero_obj(), factor, le.line_file.clone()),
                    self.strategy_less_equal_fact(scale, one_obj(), le.line_file.clone()),
                ]);
            }
        }
        if alts.is_empty() {
            return Ok(None);
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.try_strategy_requirement_alternatives(alts, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(MulScaleFactorOneOrLessLeftStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_mul_componentwise_less_equal_aligned_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<MulComponentwiseLessEqualAlignedStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(lower), Some(upper)) = (as_mul(&le.left), as_mul(&le.right)) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(zero_obj(), lower.0.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), lower.1.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(lower.0, upper.0, le.line_file.clone()),
            self.strategy_less_equal_fact(lower.1, upper.1, le.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(MulComponentwiseLessEqualAlignedStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_mul_componentwise_less_equal_crossed_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<MulComponentwiseLessEqualCrossedStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(lower), Some(upper)) = (as_mul(&le.left), as_mul(&le.right)) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(zero_obj(), lower.0.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), lower.1.clone(), le.line_file.clone()),
            self.strategy_less_equal_fact(lower.0, upper.1, le.line_file.clone()),
            self.strategy_less_equal_fact(lower.1, upper.0, le.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(MulComponentwiseLessEqualCrossedStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_common_nonnegative_factor_less_equal_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<CommonNonnegativeFactorLessEqualStrategySingleStep>> {
        let Some(le) = as_le(fact) else {
            return Ok(None);
        };
        let (Some(lm), Some(rm)) = (as_mul(&le.left), as_mul(&le.right)) else {
            return Ok(None);
        };
        let left_factors = [lm.0, lm.1];
        let right_factors = [rm.0, rm.1];
        let mut alts = Vec::new();
        for (li, lf) in left_factors.iter().enumerate() {
            for (ri, rf) in right_factors.iter().enumerate() {
                if lf != rf {
                    continue;
                }
                alts.push(vec![
                    self.strategy_less_equal_fact(zero_obj(), lf.clone(), le.line_file.clone()),
                    self.strategy_less_equal_fact(
                        left_factors[1 - li].clone(),
                        right_factors[1 - ri].clone(),
                        le.line_file.clone(),
                    ),
                ]);
            }
        }
        if alts.is_empty() {
            return Ok(None);
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.try_strategy_requirement_alternatives(alts, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(CommonNonnegativeFactorLessEqualStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

// Normalize the converse spelling locally; requirements still use the same
// bounded strategy route. Example: a >= b becomes b <= a (and > becomes <).
fn as_le(fact: &AtomicFact) -> Option<std::borrow::Cow<'_, LessEqualFact>> {
    match fact {
        AtomicFact::LessEqualFact(f) => Some(std::borrow::Cow::Borrowed(f)),
        AtomicFact::GreaterEqualFact(f) => Some(std::borrow::Cow::Owned(LessEqualFact {
            fact_id: f.fact_id,
            left: f.right.clone(),
            right: f.left.clone(),
            line_file: f.line_file.clone(),
        })),
        _ => None,
    }
}
fn as_add(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
            Some((x.left.as_ref().clone(), x.right.as_ref().clone()))
        }
        _ => None,
    }
}
fn as_sub(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
            Some((x.left.as_ref().clone(), x.right.as_ref().clone()))
        }
        _ => None,
    }
}
fn as_mul(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
            Some((x.left.as_ref().clone(), x.right.as_ref().clone()))
        }
        _ => None,
    }
}
fn as_div(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
            Some((x.left.as_ref().clone(), x.right.as_ref().clone()))
        }
        _ => None,
    }
}
fn as_pow(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
            Some((x.base.as_ref().clone(), x.exponent.as_ref().clone()))
        }
        _ => None,
    }
}
fn as_abs(obj: &Obj) -> Option<Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref().clone()),
        _ => None,
    }
}
fn pow_obj(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(exponent),
    }))
}
fn zero_le_mul(fact: &AtomicFact) -> Option<(Obj, Obj, Option<SourceLine>)> {
    let le = as_le(fact)?;
    if !is_zero_obj(&le.left) {
        return None;
    }
    let (l, r) = as_mul(&le.right)?;
    Some((l, r, le.line_file.clone()))
}
fn finite_set_constructor_children(set: &Obj) -> Option<Vec<Obj>> {
    match set {
        Obj::SetOperator(SetOperator::Union(u)) => {
            Some(vec![u.left.as_ref().clone(), u.right.as_ref().clone()])
        }
        Obj::SetOperator(SetOperator::Intersect(i)) => Some(vec![i.left.as_ref().clone()]),
        Obj::SetOperator(SetOperator::SetMinus(s)) => Some(vec![s.left.as_ref().clone()]),
        _ => None,
    }
}
