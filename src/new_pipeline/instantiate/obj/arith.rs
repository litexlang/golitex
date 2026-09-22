use std::collections::HashMap;

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::obj::{Abs, Add, Arccos, Arccot, Arcsin, Arctan, Ceil, ComplexAbs, Cos, Cot, Div, Exp, Factorial, Floor, Gcd, ImaginaryPart, Lcm, Ln, Log, Max, Min, Mod, Mul, Obj, Pow, Quot, RealPart, Sign, Sin, Sqrt, Sub, Tan, ArithmeticOperator, ComplexOperator, ExpLogOperator, IntegerOperator, TrigOperator};
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_add_obj(
        &mut self,
        a: &Add,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_sub_obj(
        &mut self,
        a: &Sub,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_mul_obj(
        &mut self,
        a: &Mul,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_div_obj(
        &mut self,
        a: &Div,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_mod_obj(
        &mut self,
        a: &Mod,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_quot_obj(
        &mut self,
        a: &Quot,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::IntegerOperator(IntegerOperator::Quot(Quot {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_gcd_obj(
        &mut self,
        a: &Gcd,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_lcm_obj(
        &mut self,
        a: &Lcm,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::IntegerOperator(IntegerOperator::Lcm(Lcm {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_min_obj(
        &mut self,
        a: &Min,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_max_obj(
        &mut self,
        a: &Max,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_pow_obj(
        &mut self,
        a: &Pow,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(self.inst_obj_rec(&a.base, param_to_arg_map)?),
            exponent: Box::new(self.inst_obj_rec(&a.exponent, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_log_obj(
        &mut self,
        a: &Log,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ExpLogOperator(ExpLogOperator::Log(Log {
            base: Box::new(self.inst_obj_rec(&a.base, param_to_arg_map)?),
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_floor_obj(
        &mut self,
        a: &Floor,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_ceil_obj(
        &mut self,
        a: &Ceil,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_exp_obj(
        &mut self,
        a: &Exp,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_ln_obj(
        &mut self,
        a: &Ln,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_sign_obj(
        &mut self,
        a: &Sign,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_factorial_obj(
        &mut self,
        a: &Factorial,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::IntegerOperator(IntegerOperator::Factorial(Factorial {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_abs_obj(
        &mut self,
        a: &Abs,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_sin_obj(
        &mut self,
        a: &Sin,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Sin(Sin {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_arcsin_obj(
        &mut self,
        a: &Arcsin,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Arcsin(Arcsin {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_arccos_obj(
        &mut self,
        a: &Arccos,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Arccos(Arccos {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_arctan_obj(
        &mut self,
        a: &Arctan,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Arctan(Arctan {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_arccot_obj(
        &mut self,
        a: &Arccot,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Arccot(Arccot {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_cos_obj(
        &mut self,
        a: &Cos,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Cos(Cos {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_tan_obj(
        &mut self,
        a: &Tan,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Tan(Tan {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_cot_obj(
        &mut self,
        a: &Cot,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::TrigOperator(TrigOperator::Cot(Cot {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_real_part_obj(
        &mut self,
        a: &RealPart,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ComplexOperator(ComplexOperator::RealPart(RealPart {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_imaginary_part_obj(
        &mut self,
        a: &ImaginaryPart,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_complex_abs_obj(
        &mut self,
        a: &ComplexAbs,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }

    pub(crate) fn inst_sqrt_obj(
        &mut self,
        a: &Sqrt,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        Ok(Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
        })))
    }
}
