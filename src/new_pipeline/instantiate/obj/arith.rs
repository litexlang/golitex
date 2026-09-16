use std::collections::HashMap;

use crate::new_pipeline::ast::obj::{
    Abs, Add, Arcsin, Ceil, ComplexAbs, Cos, Cot, Div, Exp, Factorial, Floor, Gcd, ImaginaryPart,
    Lcm, Ln, Log, Max, Min, Mod, Mul, Obj, Pow, Quot, RealPart, Sign, Sin, Sqrt, Sub, Tan,
};
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_add_obj(
        &mut self,
        a: &Add,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Add(Add {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_sub_obj(
        &mut self,
        a: &Sub,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Sub(Sub {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_mul_obj(
        &mut self,
        a: &Mul,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Mul(Mul {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_div_obj(
        &mut self,
        a: &Div,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Div(Div {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_mod_obj(
        &mut self,
        a: &Mod,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Mod(Mod {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_quot_obj(
        &mut self,
        a: &Quot,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Quot(Quot {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_gcd_obj(
        &mut self,
        a: &Gcd,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Gcd(Gcd {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_lcm_obj(
        &mut self,
        a: &Lcm,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Lcm(Lcm {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_min_obj(
        &mut self,
        a: &Min,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Min(Min {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_max_obj(
        &mut self,
        a: &Max,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Max(Max {
            left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map, fresh, binder_renames)?),
            right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_pow_obj(
        &mut self,
        a: &Pow,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Pow(Pow {
            base: Box::new(self.inst_obj_rec(&a.base, param_to_arg_map, fresh, binder_renames)?),
            exponent: Box::new(self.inst_obj_rec(&a.exponent, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_log_obj(
        &mut self,
        a: &Log,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Log(Log {
            base: Box::new(self.inst_obj_rec(&a.base, param_to_arg_map, fresh, binder_renames)?),
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_floor_obj(
        &mut self,
        a: &Floor,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Floor(Floor {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_ceil_obj(
        &mut self,
        a: &Ceil,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Ceil(Ceil {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_exp_obj(
        &mut self,
        a: &Exp,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Exp(Exp {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_ln_obj(
        &mut self,
        a: &Ln,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Ln(Ln {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_sign_obj(
        &mut self,
        a: &Sign,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Sign(Sign {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_factorial_obj(
        &mut self,
        a: &Factorial,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Factorial(Factorial {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_abs_obj(
        &mut self,
        a: &Abs,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Abs(Abs {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_sin_obj(
        &mut self,
        a: &Sin,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Sin(Sin {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_arcsin_obj(
        &mut self,
        a: &Arcsin,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Arcsin(Arcsin {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_cos_obj(
        &mut self,
        a: &Cos,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Cos(Cos {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_tan_obj(
        &mut self,
        a: &Tan,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Tan(Tan {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_cot_obj(
        &mut self,
        a: &Cot,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Cot(Cot {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_real_part_obj(
        &mut self,
        a: &RealPart,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::RealPart(RealPart {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_imaginary_part_obj(
        &mut self,
        a: &ImaginaryPart,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::ImaginaryPart(ImaginaryPart {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_complex_abs_obj(
        &mut self,
        a: &ComplexAbs,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::ComplexAbs(ComplexAbs {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }

    pub(crate) fn inst_sqrt_obj(
        &mut self,
        a: &Sqrt,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::Sqrt(Sqrt {
            arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map, fresh, binder_renames)?),
        }))
    }
}
