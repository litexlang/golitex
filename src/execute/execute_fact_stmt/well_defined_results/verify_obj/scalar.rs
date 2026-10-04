//! Scalar object WD (P0): children + carrier / domain requirement facts.
//! Ported from verification/well_definedness/object/scalar.rs.

use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::fact::{AndChainAtomicFact, AtomicFact, GreaterFact, LessEqualFact, NotEqualFact, OrFact, QuantifierFreeFact};
use crate::ast::obj::StandardSet;
use crate::ast::obj::{Abs, Add, Arccos, Arccot, Arcsin, Arctan, Ceil, ComplexAbs, Cos, Cot, Div, Exp, Factorial, Floor, Gcd, ImaginaryPart, Lcm, Ln, Log, Max, Min, Mod, Mul, Neg, Number, Obj, Pow, Quot, RealPart, Sign, Sin, Sqrt, Sub, Tan, IntegerOperator, Literal, TrigOperator};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::exact_rational::EvalRational;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_number_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    pub(super) fn verify_imaginary_unit_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    pub(super) fn verify_euler_number_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    pub(super) fn verify_pi_obj_well_definedness_by_def(
        &mut self,
        _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        Ok(ObjWellDefinedByDefCommonStages::leaf())
    }

    pub(super) fn verify_add_obj_well_definedness_by_def(
        &mut self,
        value: &Add,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_in_c_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    pub(super) fn verify_sub_obj_well_definedness_by_def(
        &mut self,
        value: &Sub,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_in_c_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    pub(super) fn verify_neg_obj_well_definedness_by_def(
        &mut self,
        value: &Neg,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof =
            self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let req = self.require_obj_in_c(value.arg.as_ref(), verify_state)?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    pub(super) fn verify_mul_obj_well_definedness_by_def(
        &mut self,
        value: &Mul,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_in_c_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }

    pub(super) fn verify_div_obj_well_definedness_by_def(
        &mut self,
        value: &Div,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state.clone(),
        )?;
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.right.as_ref().clone(),
            right: zero,
            line_file: None,
        });
        let mut reqs = Vec::new();
        reqs.push(self.verify_required_atomic_fact(
            nonzero,
            verify_state.clone(),
            "divisor must be non-zero".to_string(),
        )?);
        reqs.push(self.require_obj_in_c(value.left.as_ref(), verify_state.clone())?);
        reqs.push(self.require_obj_in_c(value.right.as_ref(), verify_state)?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_mod_obj_well_definedness_by_def(
        &mut self,
        value: &Mod,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.left.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "mod dividend must belong to Z".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.right.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "mod modulus must belong to Z".to_string(),
        )?);
        if !matches!(value.right.as_ref(), Obj::IntegerOperator(IntegerOperator::Gcd(_))) {
            let zero = Obj::Literal(Literal::Number(Number {
                normalized_value: "0".to_string(),
            }));
            let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: value.right.as_ref().clone(),
                right: zero,
                line_file: None,
            });
            reqs.push(self.verify_required_atomic_fact(
                nonzero,
                verify_state,
                format!("modulus must be non-zero"),
            )?);
        }
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_quot_obj_well_definedness_by_def(
        &mut self,
        value: &Quot,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.left.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "quot dividend must belong to Z".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.right.as_ref(),
            StandardSet::NPos,
            verify_state,
            "quot divisor must belong to N+".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_gcd_obj_well_definedness_by_def(
        &mut self,
        value: &Gcd,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.left.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "gcd left argument must belong to Z".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.right.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "gcd right argument must belong to Z".to_string(),
        )?);
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let left_nz = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.left.as_ref().clone(),
            right: zero.clone(),
            line_file: None,
        });
        let right_nz = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.right.as_ref().clone(),
            right: zero,
            line_file: None,
        });
        // The domain excludes only the all-zero pair. A checked disjunction
        // suffices without selecting either nonzero operand.
        // Either branch order certifies the same nonzero-pair domain. Keep
        // the proof of the actually checked disjunction, without choosing a
        // nonzero operand or treating Or citation as order-independent.
        for (first, second) in [(&left_nz, &right_nz), (&right_nz, &left_nz)] {
            let non_all_zero = QuantifierFreeFact::OrFact(OrFact {
                fact_id: self.global_ids.allocate_fact_id(),
                facts: vec![AndChainAtomicFact::AtomicFact(first.clone()), AndChainAtomicFact::AtomicFact(second.clone())],
                line_file: None,
            });
            let disjunction = self.verify_required_quantifier_free_fact(
                non_all_zero, verify_state.clone(),
            )?;
            if !disjunction.is_failed() {
                reqs.push(disjunction);
                return Ok(self.with_requirements(proof, reqs));
            }
        }
        let left_r = self.verify_required_atomic_fact(
            left_nz,
            verify_state.clone(),
            "gcd left nonzero".to_string(),
        )?;
        if !left_r.is_failed() {
            reqs.push(left_r);
            return Ok(self.with_requirements(proof, reqs));
        }
        let right_r = self.verify_required_atomic_fact(
            right_nz,
            verify_state,
            "gcd right nonzero".to_string(),
        )?;
        if !right_r.is_failed() {
            reqs.push(right_r);
            return Ok(self.with_requirements(proof, reqs));
        }
        // Neither nonzero obligation proved: keep a failed requirement so
        // entry collapses soft misses to FailToVerifyWellDefined(Requirement { ... }).
        reqs.push(left_r);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_lcm_obj_well_definedness_by_def(
        &mut self,
        value: &Lcm,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.left.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "lcm left argument must belong to Z".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.right.as_ref(),
            StandardSet::Z,
            verify_state,
            "lcm right argument must belong to Z".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_abs_obj_well_definedness_by_def(
        &mut self,
        value: &Abs,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "abs",
            verify_state,
        )
    }

    pub(super) fn verify_floor_obj_well_definedness_by_def(
        &mut self,
        value: &Floor,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "floor",
            verify_state,
        )
    }

    pub(super) fn verify_ceil_obj_well_definedness_by_def(
        &mut self,
        value: &Ceil,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "ceil",
            verify_state,
        )
    }

    pub(super) fn verify_min_obj_well_definedness_by_def(
        &mut self,
        value: &Min,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_carrier_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            StandardSet::R,
            verify_state,
        )
    }

    pub(super) fn verify_max_obj_well_definedness_by_def(
        &mut self,
        value: &Max,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_carrier_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            StandardSet::R,
            verify_state,
        )
    }

    pub(super) fn verify_exp_obj_well_definedness_by_def(
        &mut self,
        value: &Exp,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "exp",
            verify_state,
        )
    }

    pub(super) fn verify_ln_obj_well_definedness_by_def(
        &mut self,
        value: &Ln,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        // Domain is the positive reals R+. Example: `ln(e)` after `e $in R+`.
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::RPos,
            "ln",
            verify_state,
        )
    }

    pub(super) fn verify_sign_obj_well_definedness_by_def(
        &mut self,
        value: &Sign,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "sign",
            verify_state,
        )
    }

    pub(super) fn verify_factorial_obj_well_definedness_by_def(
        &mut self,
        value: &Factorial,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::N,
            "factorial",
            verify_state,
        )
    }

    pub(super) fn verify_pow_obj_well_definedness_by_def(
        &mut self,
        value: &Pow,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        // Closed Q+×Q also permits noninteger exponents, independently of
        // whether the exact result is rational. Example: 8^(1/3) and 2^(1/3).
        // Existing domains: R×N, C×N, then C×Z×base≠0.
        // Example: `sin(x)^2` is WD from `sin(x) $in R` and `2 $in N`.
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.base.as_ref(),
            value.exponent.as_ref(),
            verify_state.clone(),
        )?;
        if let (Some(base), Some(exponent)) = (
            EvalRational::from_obj(value.base.as_ref()),
            EvalRational::from_obj(value.exponent.as_ref()),
        ) {
            if !base.is_zero() && !base.is_negative() && exponent.to_i128_if_integer().is_none() {
                let reqs = self.try_pow_domain_positive_rational(value, verify_state)?;
                return Ok(self.with_requirements(proof, reqs));
            }
        }
        let reqs_r = self.try_pow_domain_real_natural(value, verify_state.clone())?;
        if reqs_r.iter().all(|r| !r.is_failed()) {
            return Ok(self.with_requirements(proof, reqs_r));
        }
        let reqs_n = self.try_pow_domain_complex_natural(value, verify_state.clone())?;
        if reqs_n.iter().all(|r| !r.is_failed()) {
            return Ok(self.with_requirements(proof, reqs_n));
        }
        let reqs_z = self.try_pow_domain_nonzero_complex_integer(value, verify_state)?;
        if reqs_z.iter().all(|r| !r.is_failed()) {
            return Ok(self.with_requirements(proof, reqs_z));
        }
        // No pow domain branch proved: keep failed requirements for collapse.
        Ok(self.with_requirements(proof, reqs_z))
    }

    pub(super) fn verify_sin_obj_well_definedness_by_def(
        &mut self,
        value: &Sin,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "sin",
            verify_state,
        )
    }

    pub(super) fn verify_arcsin_obj_well_definedness_by_def(
        &mut self,
        value: &Arcsin,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "arcsin argument must belong to R".to_string(),
        )?);
        let neg_one = Obj::Literal(Literal::Number(Number {
            normalized_value: "-1".to_string(),
        }));
        let one = Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        }));
        let lo = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: neg_one,
            right: value.arg.as_ref().clone(),
            line_file: None,
        });
        let hi = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.arg.as_ref().clone(),
            right: one,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            lo,
            verify_state.clone(),
            "arcsin: argument must be >= -1".to_string(),
        )?);
        reqs.push(self.verify_required_atomic_fact(
            hi,
            verify_state,
            "arcsin: argument must be <= 1".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_arccos_obj_well_definedness_by_def(
        &mut self,
        value: &Arccos,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "arccos argument must belong to R".to_string(),
        )?);
        let neg_one = Obj::Literal(Literal::Number(Number {
            normalized_value: "-1".to_string(),
        }));
        let one = Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        }));
        let lo = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: neg_one,
            right: value.arg.as_ref().clone(),
            line_file: None,
        });
        let hi = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.arg.as_ref().clone(),
            right: one,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            lo,
            verify_state.clone(),
            "arccos: argument must be >= -1".to_string(),
        )?);
        reqs.push(self.verify_required_atomic_fact(
            hi,
            verify_state,
            "arccos: argument must be <= 1".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_arctan_obj_well_definedness_by_def(
        &mut self,
        value: &Arctan,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "arctan",
            verify_state,
        )
    }

    pub(super) fn verify_arccot_obj_well_definedness_by_def(
        &mut self,
        value: &Arccot,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "arccot",
            verify_state,
        )
    }

    pub(super) fn verify_cos_obj_well_definedness_by_def(
        &mut self,
        value: &Cos,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::R,
            "cos",
            verify_state,
        )
    }

    pub(super) fn verify_tan_obj_well_definedness_by_def(
        &mut self,
        value: &Tan,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "tan argument must belong to R".to_string(),
        )?);
        // Principal arctan range is open around ±pi/2, so cos(arctan(x)) != 0.
        if matches!(value.arg.as_ref(), Obj::TrigOperator(TrigOperator::Arctan(_))) {
            return Ok(self.with_requirements(proof, reqs));
        }
        let denom = Obj::TrigOperator(TrigOperator::Cos(Cos {
            arg: Box::new(value.arg.as_ref().clone()),
        }));
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: denom,
            right: zero,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            nonzero,
            verify_state,
            "tan requires cos(arg) != 0".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_cot_obj_well_definedness_by_def(
        &mut self,
        value: &Cot,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "cot argument must belong to R".to_string(),
        )?);
        // Principal arccot range is (0, pi), so sin(arccot(x)) != 0.
        if matches!(value.arg.as_ref(), Obj::TrigOperator(TrigOperator::Arccot(_))) {
            return Ok(self.with_requirements(proof, reqs));
        }
        let denom = Obj::TrigOperator(TrigOperator::Sin(Sin {
            arg: Box::new(value.arg.as_ref().clone()),
        }));
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: denom,
            right: zero,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            nonzero,
            verify_state,
            "cot requires sin(arg) != 0".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_real_part_obj_well_definedness_by_def(
        &mut self,
        value: &RealPart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::C,
            "real_part",
            verify_state,
        )
    }

    pub(super) fn verify_imaginary_part_obj_well_definedness_by_def(
        &mut self,
        value: &ImaginaryPart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::C,
            "imaginary_part",
            verify_state,
        )
    }

    pub(super) fn verify_complex_abs_obj_well_definedness_by_def(
        &mut self,
        value: &ComplexAbs,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_carrier_obj_well_definedness_by_def(
            value.arg.as_ref(),
            StandardSet::C,
            "complex_abs",
            verify_state,
        )
    }

    pub(super) fn verify_sqrt_obj_well_definedness_by_def(
        &mut self,
        value: &Sqrt,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "sqrt argument must belong to R".to_string(),
        )?);
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let ge = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero,
            right: value.arg.as_ref().clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            ge,
            verify_state,
            "sqrt: argument must be >= 0".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    pub(super) fn verify_log_obj_well_definedness_by_def(
        &mut self,
        value: &Log,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.base.as_ref(),
            value.arg.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.base.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "log base must belong to R".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.arg.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "log argument must belong to R".to_string(),
        )?);
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let one = Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        }));
        let base_pos = AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.base.as_ref().clone(),
            right: zero.clone(),
            line_file: None,
        });
        let arg_pos = AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.arg.as_ref().clone(),
            right: zero,
            line_file: None,
        });
        let base_ne_one = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.base.as_ref().clone(),
            right: one,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            base_pos,
            verify_state.clone(),
            "log: base must be > 0".to_string(),
        )?);
        reqs.push(self.verify_required_atomic_fact(
            arg_pos,
            verify_state.clone(),
            "log: argument must be > 0".to_string(),
        )?);
        reqs.push(self.verify_required_atomic_fact(
            base_ne_one,
            verify_state,
            "log: base must be != 1".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    fn verify_binary_in_c_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof =
            self.verify_binary_obj_well_definedness_by_def(left, right, verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_c(left, verify_state.clone())?);
        reqs.push(self.require_obj_in_c(right, verify_state)?);
        Ok(self.with_requirements(proof, reqs))
    }

    fn verify_unary_carrier_obj_well_definedness_by_def(
        &mut self,
        arg: &Obj,
        carrier: StandardSet,
        name: &str,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_unary_obj_well_definedness_by_def(arg, verify_state.clone())?;
        let req = self.require_obj_in_standard_set(
            arg,
            carrier,
            verify_state,
            format!("{name} argument must belong to the required carrier"),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    fn verify_binary_carrier_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        carrier: StandardSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof =
            self.verify_binary_obj_well_definedness_by_def(left, right, verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            left,
            carrier.clone(),
            verify_state.clone(),
            "obj must belong to required carrier".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            right,
            carrier,
            verify_state,
            "obj must belong to required carrier".to_string(),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    fn try_pow_domain_positive_rational(
        &mut self,
        value: &Pow,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.base.as_ref(),
            StandardSet::QPos,
            verify_state.clone(),
            "closed rational power base must belong to Q+".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.exponent.as_ref(),
            StandardSet::Q,
            verify_state,
            "closed rational power exponent must belong to Q".to_string(),
        )?);
        Ok(reqs)
    }

    fn try_pow_domain_real_natural(
        &mut self,
        value: &Pow,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.base.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            "pow base must belong to R".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.exponent.as_ref(),
            StandardSet::N,
            verify_state,
            "pow exponent must belong to N".to_string(),
        )?);
        Ok(reqs)
    }

    fn try_pow_domain_complex_natural(
        &mut self,
        value: &Pow,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.base.as_ref(),
            StandardSet::C,
            verify_state.clone(),
            "pow base must belong to C".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.exponent.as_ref(),
            StandardSet::N,
            verify_state,
            "pow exponent must belong to N".to_string(),
        )?);
        Ok(reqs)
    }

    fn try_pow_domain_nonzero_complex_integer(
        &mut self,
        value: &Pow,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.base.as_ref(),
            StandardSet::C,
            verify_state.clone(),
            "pow base must belong to C".to_string(),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.exponent.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            "pow exponent must belong to Z".to_string(),
        )?);
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let nonzero = AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.base.as_ref().clone(),
            right: zero,
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            nonzero,
            verify_state,
            "pow base must be non-zero for integer exponent".to_string(),
        )?);
        Ok(reqs)
    }
}
