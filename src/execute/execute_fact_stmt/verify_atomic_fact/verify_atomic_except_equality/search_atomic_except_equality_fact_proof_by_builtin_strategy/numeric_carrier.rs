use super::helper::{one_obj, zero_obj};
use super::result::*;
use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{
    ArithmeticOperator, FiniteSetStat, IntegerOperator, Obj, SetFormer, SetOperator, StandardSet,
};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_finite_set_size_in_numeric_carrier_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<FiniteSetSizeInNumericCarrierStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(target) = &inf.set else { return Ok(None); };
        if !matches!(target, StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C) {
            return Ok(None);
        }
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = &inf.element else { return Ok(None); };
        let requirements = vec![self.strategy_is_finite_set_fact(size.set.as_ref().clone(), inf.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(FiniteSetSizeInNumericCarrierStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_finite_extremum_source_in_carrier_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<FiniteExtremumSourceInCarrierStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(target) = &inf.set else { return Ok(None); };
        if !matches!(target, StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C) {
            return Ok(None);
        }
        let set = match &inf.element {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(x)) => x.set.as_ref(),
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(x)) => x.set.as_ref(),
            _ => return Ok(None),
        };
        let Some(requirements) = self.finite_extremum_carrier_requirements(set, target, &inf.line_file) else {
            return Ok(None);
        };
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(FiniteExtremumSourceInCarrierStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_refined_numeric_carrier_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RefinedNumericCarrierStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(target) = &inf.set else { return Ok(None); };
        let Some(requirements) = refined_numeric_carrier_requirements(self, inf, target) else {
            return Ok(None);
        };
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RefinedNumericCarrierStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }


    pub(super) fn search_real_arithmetic_carrier_closure_add_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RealArithmeticCarrierClosureAddStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::R) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::R, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RealArithmeticCarrierClosureAddStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_real_arithmetic_carrier_closure_sub_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RealArithmeticCarrierClosureSubStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::R) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_sub(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::R, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RealArithmeticCarrierClosureSubStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_real_arithmetic_carrier_closure_mul_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RealArithmeticCarrierClosureMulStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::R) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mul(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::R, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RealArithmeticCarrierClosureMulStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_real_arithmetic_carrier_closure_div_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RealArithmeticCarrierClosureDivStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::R) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_div(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::R, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RealArithmeticCarrierClosureDivStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_real_arithmetic_carrier_closure_pow_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RealArithmeticCarrierClosurePowStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::R) = &inf.set else { return Ok(None); };
        let Some((base, _)) = as_pow(&inf.element) else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(base, Obj::StandardSet(StandardSet::R), inf.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RealArithmeticCarrierClosurePowStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_add_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosureAddStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Q, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosureAddStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_sub_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosureSubStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_sub(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Q, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosureSubStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_mul_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosureMulStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mul(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Q, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosureMulStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_div_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosureDivStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_div(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Q, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosureDivStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_pow_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosurePowStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some((base, exponent)) = as_pow(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(base, Obj::StandardSet(StandardSet::Q), inf.line_file.clone()),
            self.strategy_in_fact(exponent, Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosurePowStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_rational_arithmetic_carrier_closure_abs_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalArithmeticCarrierClosureAbsStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Q) = &inf.set else { return Ok(None); };
        let Some(arg) = as_abs(&inf.element) else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(arg, Obj::StandardSet(StandardSet::Q), inf.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(RationalArithmeticCarrierClosureAbsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_add_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosureAddStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Z, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosureAddStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_sub_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosureSubStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_sub(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Z, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosureSubStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_mul_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosureMulStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mul(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Z, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosureMulStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_mod_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosureModStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mod(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::Z, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosureModStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_pow_nat_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosurePowNatStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some((base, exponent)) = as_pow(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(base, Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_in_fact(exponent, Obj::StandardSet(StandardSet::N), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosurePowNatStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_integer_arithmetic_carrier_closure_abs_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntegerArithmeticCarrierClosureAbsStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::Z) = &inf.set else { return Ok(None); };
        let Some(arg) = as_abs(&inf.element) else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(arg, Obj::StandardSet(StandardSet::Z), inf.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntegerArithmeticCarrierClosureAbsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_natural_arithmetic_carrier_closure_add_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NaturalArithmeticCarrierClosureAddStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::N) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::N, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(NaturalArithmeticCarrierClosureAddStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_natural_arithmetic_carrier_closure_mul_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NaturalArithmeticCarrierClosureMulStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::N) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mul(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::N, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(NaturalArithmeticCarrierClosureMulStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_natural_arithmetic_carrier_closure_sub_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NaturalArithmeticCarrierClosureSubStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::N) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_sub(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(left.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_in_fact(right.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_equal_fact(right, left, inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(NaturalArithmeticCarrierClosureSubStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_natural_arithmetic_carrier_closure_pow_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NaturalArithmeticCarrierClosurePowStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::N) = &inf.set else { return Ok(None); };
        let Some((base, exponent)) = as_pow(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, base, exponent, StandardSet::N, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(NaturalArithmeticCarrierClosurePowStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_natural_arithmetic_carrier_closure_abs_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NaturalArithmeticCarrierClosureAbsStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::N) = &inf.set else { return Ok(None); };
        let Some(arg) = as_abs(&inf.element) else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(arg, Obj::StandardSet(StandardSet::Z), inf.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(NaturalArithmeticCarrierClosureAbsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_add_left_pos_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierAddLeftPosStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(left, Obj::StandardSet(StandardSet::NPos), inf.line_file.clone()),
            self.strategy_in_fact(right, Obj::StandardSet(StandardSet::N), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierAddLeftPosStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_add_right_pos_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierAddRightPosStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_add(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(left, Obj::StandardSet(StandardSet::N), inf.line_file.clone()),
            self.strategy_in_fact(right, Obj::StandardSet(StandardSet::NPos), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierAddRightPosStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_mul_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierMulStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Some((left, right)) = as_mul(&inf.element) else { return Ok(None); };
        let requirements = binary_in_requirements(self, left, right, StandardSet::NPos, inf.line_file.clone());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierMulStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_pow_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierPowStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Some((base, exponent)) = as_pow(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(base, Obj::StandardSet(StandardSet::NPos), inf.line_file.clone()),
            self.strategy_in_fact(exponent, Obj::StandardSet(StandardSet::N), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierPowStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_abs_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierAbsStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Some(arg) = as_abs(&inf.element) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(arg, Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_fact(zero_obj(), inf.element.clone(), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierAbsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_positive_natural_carrier_finite_set_size_strategy(
        &mut self, fact: &AtomicFact, ctx: StrategySearch,
    ) -> RuntimeResult<Option<PositiveNaturalCarrierFiniteSetSizeStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(StandardSet::NPos) = &inf.set else { return Ok(None); };
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) = &inf.element else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::N), inf.line_file.clone()),
            self.strategy_less_equal_fact(one_obj(), inf.element.clone(), inf.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PositiveNaturalCarrierFiniteSetSizeStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    fn finite_extremum_carrier_requirements(
        &mut self,
        set: &Obj,
        target: &StandardSet,
        line_file: &Option<SourceLine>,
    ) -> Option<Vec<Fact>> {
        let target_obj = Obj::StandardSet(target.clone());
        match set {
            Obj::SetFormer(SetFormer::ListSet(list)) => {
                let mut out = Vec::new();
                for element in &list.list {
                    out.push(self.strategy_in_fact(element.as_ref().clone(), target_obj.clone(), line_file.clone()));
                }
                Some(out)
            }
            Obj::SetOperator(SetOperator::Union(u)) => {
                let mut out = Vec::new();
                for part in [u.left.as_ref(), u.right.as_ref()] {
                    out.extend(self.finite_extremum_carrier_requirements(part, target, line_file)?);
                }
                Some(out)
            }
            Obj::SetOperator(SetOperator::Intersect(i)) => {
                self.finite_extremum_carrier_requirements(i.left.as_ref(), target, line_file)
            }
            Obj::SetOperator(SetOperator::SetMinus(s)) => {
                self.finite_extremum_carrier_requirements(s.left.as_ref(), target, line_file)
            }
            Obj::SetFormer(SetFormer::SetBuilder(b)) => {
                self.finite_extremum_carrier_requirements(b.param_set.as_ref(), target, line_file)
            }
            _ => Some(vec![self.strategy_subset_fact(set.clone(), target_obj, line_file.clone())]),
        }
    }
}

fn as_in(fact: &AtomicFact) -> Option<&InFact> {
    match fact { AtomicFact::InFact(f) => Some(f), _ => None }
}

fn refined_numeric_carrier_requirements(
    runtime: &mut Runtime,
    fact: &InFact,
    target: &StandardSet,
) -> Option<Vec<Fact>> {
    let element = fact.element.clone();
    let lf = fact.line_file.clone();
    let (base, condition) = match target {
        StandardSet::QPos => (StandardSet::Q, runtime.strategy_less_fact(zero_obj(), element.clone(), lf.clone())),
        StandardSet::RPos => (StandardSet::R, runtime.strategy_less_fact(zero_obj(), element.clone(), lf.clone())),
        StandardSet::QNeg => (StandardSet::Q, runtime.strategy_less_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::ZNeg => (StandardSet::Z, runtime.strategy_less_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::RNeg => (StandardSet::R, runtime.strategy_less_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::QStar => (StandardSet::Q, runtime.strategy_not_equal_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::ZStar => (StandardSet::Z, runtime.strategy_not_equal_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::RStar => (StandardSet::R, runtime.strategy_not_equal_fact(element.clone(), zero_obj(), lf.clone())),
        StandardSet::CStar => (StandardSet::C, runtime.strategy_not_equal_fact(element.clone(), zero_obj(), lf.clone())),
        _ => return None,
    };
    Some(vec![runtime.strategy_in_fact(element, Obj::StandardSet(base), lf), condition])
}

fn binary_in_requirements(
    runtime: &mut Runtime, left: Obj, right: Obj, carrier: StandardSet, line_file: Option<SourceLine>,
) -> Vec<Fact> {
    vec![
        runtime.strategy_in_fact(left, Obj::StandardSet(carrier.clone()), line_file.clone()),
        runtime.strategy_in_fact(right, Obj::StandardSet(carrier), line_file),
    ]
}

fn as_add(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_sub(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_mul(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_div(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_pow(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => Some((x.base.as_ref().clone(), x.exponent.as_ref().clone())), _ => None }
}
fn as_abs(obj: &Obj) -> Option<Obj> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Abs(x)) => Some(x.arg.as_ref().clone()), _ => None }
}
fn as_mod(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::IntegerOperator(IntegerOperator::Mod(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
