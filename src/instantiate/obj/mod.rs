use crate::ast::obj::{
    Conjugate, Cosh, Coth, Csc, Csch, HyperbolicOperator, Sec, Sech, Sinh, SymmetricDifference,
    Tanh,
};
mod arith;
mod atom;
mod binder_obj;
mod set;
mod struct_template;

use std::collections::HashMap;

use crate::runtime::runtime_ids::IdentifierId;

use crate::ast::obj::{
    ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FunctionSpace,
    IntegerOperator, IteratedOperator, Literal, Obj, ProductShape, SetFormer, SetOperator,
    StructAndFieldAccessObj, TrigOperator,
};
use crate::runtime::Runtime;

use super::error::InstError;

impl Runtime {
    pub(crate) fn inst_obj_rec(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Obj, InstError> {
        match obj {
            Obj::LimitOperator(crate::ast::obj::LimitOperator::MultivariableScalar(_))
            | Obj::LimitOperator(crate::ast::obj::LimitOperator::MultivariableVector(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Partial(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::ScalarDifferential(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::TotalDifferential(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Gradient(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Jacobian(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Hessian(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Divergence(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Curl(_))
            | Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::Laplacian(_)) => {
                let mut args = Vec::new();
                for arg in obj.multivariable_selector_args().unwrap() {
                    args.push(self.inst_obj_rec(arg, param_to_arg_map)?);
                }
                Ok(Obj::from_multivariable_selector(
                    obj.multivariable_selector_name().unwrap(),
                    &args,
                )
                .unwrap())
            }
            Obj::MatrixOperator(value) => value
                .try_map_operands(|arg| self.inst_obj_rec(arg, param_to_arg_map))
                .map(Obj::MatrixOperator),
            Obj::SetFormer(SetFormer::MatrixSet(value)) => Ok(Obj::SetFormer(
                SetFormer::MatrixSet(crate::ast::obj::MatrixSet {
                    set: Box::new(self.inst_obj_rec(&value.set, param_to_arg_map)?),
                    rows: Box::new(self.inst_obj_rec(&value.rows, param_to_arg_map)?),
                    cols: Box::new(self.inst_obj_rec(&value.cols, param_to_arg_map)?),
                }),
            )),
            Obj::IntegralOperator(crate::ast::obj::IntegralOperator::Riemann(a)) => {
                Ok(crate::ast::obj::RiemannIntegral::new(
                    self.inst_obj_rec(&a.function, param_to_arg_map)?,
                    self.inst_obj_rec(&a.lower, param_to_arg_map)?,
                    self.inst_obj_rec(&a.upper, param_to_arg_map)?,
                )
                .into())
            }
            Obj::DerivativeOperator(crate::ast::obj::DerivativeOperator::AtPoint(a)) => {
                Ok(crate::ast::obj::DerivativeAt::new(
                    self.inst_obj_rec(&a.function, param_to_arg_map)?,
                    self.inst_obj_rec(&a.point, param_to_arg_map)?,
                )
                .into())
            }
            Obj::BoundOperator(crate::ast::obj::BoundOperator::Supremum(a)) => Ok(
                crate::ast::obj::Supremum::new(self.inst_obj_rec(&a.set, param_to_arg_map)?).into(),
            ),
            Obj::BoundOperator(crate::ast::obj::BoundOperator::Infimum(a)) => Ok(
                crate::ast::obj::Infimum::new(self.inst_obj_rec(&a.set, param_to_arg_map)?).into(),
            ),
            Obj::LimitOperator(crate::ast::obj::LimitOperator::Function(a)) => {
                Ok(crate::ast::obj::FunctionLimit::with_approach(
                    self.inst_obj_rec(&a.function, param_to_arg_map)?,
                    a.approach
                        .try_map_point(|point| self.inst_obj_rec(point, param_to_arg_map))?,
                )
                .into())
            }
            Obj::LimitOperator(crate::ast::obj::LimitOperator::Sequence(a)) => {
                Ok(crate::ast::obj::SequenceLimit::new(
                    self.inst_obj_rec(&a.sequence, param_to_arg_map)?,
                )
                .into())
            }
            Obj::LimitOperator(crate::ast::obj::LimitOperator::SequenceLimsup(a)) => {
                Ok(crate::ast::obj::SequenceLimsup::new(
                    self.inst_obj_rec(&a.sequence, param_to_arg_map)?,
                )
                .into())
            }
            Obj::LimitOperator(crate::ast::obj::LimitOperator::SequenceLiminf(a)) => {
                Ok(crate::ast::obj::SequenceLiminf::new(
                    self.inst_obj_rec(&a.sequence, param_to_arg_map)?,
                )
                .into())
            }
            Obj::Identifier(_) => self.inst_identifier_obj(obj, param_to_arg_map),
            Obj::Literal(Literal::Number(_))
            | Obj::Literal(Literal::ImaginaryUnit(_))
            | Obj::Literal(Literal::EulerNumber(_))
            | Obj::Literal(Literal::Pi(_))
            | Obj::StandardSet(_) => Ok(Self::inst_leaf_obj(obj)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                self.inst_add_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
                self.inst_sub_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => {
                self.inst_neg_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
                self.inst_mul_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
                self.inst_div_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Mod(a)) => self.inst_mod_obj(a, param_to_arg_map),
            Obj::IntegerOperator(IntegerOperator::Quot(a)) => {
                self.inst_quot_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(a)) => self.inst_gcd_obj(a, param_to_arg_map),
            Obj::IntegerOperator(IntegerOperator::Lcm(a)) => self.inst_lcm_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Min(a)) => {
                self.inst_min_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(a)) => {
                self.inst_max_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
                self.inst_pow_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(a)) => self.inst_log_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)) => {
                self.inst_floor_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)) => {
                self.inst_ceil_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(a)) => self.inst_exp_obj(a, param_to_arg_map),
            Obj::ExpLogOperator(ExpLogOperator::Ln(a)) => self.inst_ln_obj(a, param_to_arg_map),
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(a)) => {
                self.inst_sign_obj(a, param_to_arg_map)
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(a)) => {
                self.inst_factorial_obj(a, param_to_arg_map)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                self.inst_abs_obj(a, param_to_arg_map)
            }
            Obj::TrigOperator(TrigOperator::Sec(a)) => {
                Ok(Sec::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::TrigOperator(TrigOperator::Csc(a)) => {
                Ok(Csc::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::ComplexOperator(ComplexOperator::Conjugate(a)) => {
                Ok(Conjugate::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Sinh(a)) => {
                Ok(Sinh::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Cosh(a)) => {
                Ok(Cosh::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Tanh(a)) => {
                Ok(Tanh::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Coth(a)) => {
                Ok(Coth::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Sech(a)) => {
                Ok(Sech::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Csch(a)) => {
                Ok(Csch::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?).into())
            }
            Obj::SetOperator(SetOperator::SymmetricDifference(a)) => Ok(SymmetricDifference::new(
                self.inst_obj_rec(&a.left, param_to_arg_map)?,
                self.inst_obj_rec(&a.right, param_to_arg_map)?,
            )
            .into()),
            Obj::TrigOperator(TrigOperator::Sin(a)) => self.inst_sin_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arcsin(a)) => self.inst_arcsin_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arccos(a)) => self.inst_arccos_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arctan(a)) => self.inst_arctan_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Arccot(a)) => self.inst_arccot_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Cos(a)) => self.inst_cos_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Tan(a)) => self.inst_tan_obj(a, param_to_arg_map),
            Obj::TrigOperator(TrigOperator::Cot(a)) => self.inst_cot_obj(a, param_to_arg_map),
            Obj::ComplexOperator(ComplexOperator::RealPart(a)) => {
                self.inst_real_part_obj(a, param_to_arg_map)
            }
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(a)) => {
                self.inst_imaginary_part_obj(a, param_to_arg_map)
            }
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(a)) => {
                self.inst_complex_abs_obj(a, param_to_arg_map)
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)) => self.inst_sqrt_obj(a, param_to_arg_map),
            Obj::SetOperator(SetOperator::Union(a)) => self.inst_union_obj(a, param_to_arg_map),
            Obj::SetOperator(SetOperator::Intersect(a)) => {
                self.inst_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::SetMinus(a)) => {
                self.inst_set_minus_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::FamilyUnion(a)) => {
                self.inst_family_union_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::FamilyIntersect(a)) => {
                self.inst_family_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexUnion(a)) => {
                self.inst_index_union_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexIntersect(a)) => {
                self.inst_index_intersect_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::PowerSet(a)) => {
                self.inst_power_set_obj(a, param_to_arg_map)
            }
            Obj::SetOperator(SetOperator::IndexCart(a)) => {
                self.inst_index_cart_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::ListSet(a)) => self.inst_list_set_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::Cart(a)) => self.inst_cart_obj(a, param_to_arg_map),
            Obj::ProductShape(ProductShape::Tuple(a)) => self.inst_tuple_obj(a, param_to_arg_map),
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(a)) => {
                self.inst_finite_set_size_obj(a, param_to_arg_map)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(a)) => {
                self.inst_finite_set_max_obj(a, param_to_arg_map)
            }
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(a)) => {
                self.inst_finite_set_min_obj(a, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::Composition(a)) => {
                Ok(crate::ast::obj::Composition::new(
                    self.inst_obj_rec(&a.outer, param_to_arg_map)?,
                    self.inst_obj_rec(&a.inner, param_to_arg_map)?,
                )
                .into())
            }
            Obj::FunctionSpace(FunctionSpace::Preimage(a)) => Ok(crate::ast::obj::Preimage::new(
                self.inst_obj_rec(&a.function, param_to_arg_map)?,
                self.inst_obj_rec(&a.value, param_to_arg_map)?,
            )
            .into()),
            Obj::FunctionSpace(FunctionSpace::PreimageSet(a)) => {
                Ok(crate::ast::obj::PreimageSet::new(
                    self.inst_obj_rec(&a.function, param_to_arg_map)?,
                    self.inst_obj_rec(&a.target_set, param_to_arg_map)?,
                )
                .into())
            }
            Obj::FunctionSpace(FunctionSpace::FnRange(a)) => {
                self.inst_fn_range_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Sum(a)) => {
                self.inst_sum_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(a)) => {
                self.inst_sum_of_finite_set_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Product(a)) => {
                self.inst_product_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(a)) => {
                self.inst_product_of_finite_set_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::Reduce(a)) => {
                self.inst_reduce_obj(a, param_to_arg_map)
            }
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(a)) => {
                self.inst_finite_set_reduce_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::Range(a)) => self.inst_range_obj(a, param_to_arg_map),
            Obj::SetFormer(SetFormer::ClosedRange(a)) => {
                self.inst_closed_range_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(a)) => {
                self.inst_finite_seq_set_obj(a, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::SeqSet(a)) => self.inst_seq_set_obj(a, param_to_arg_map),
            Obj::FnObj(f) => self.inst_fn_obj(f, param_to_arg_map),
            Obj::SetFormer(SetFormer::SetBuilder(sb)) => {
                self.inst_set_builder_obj(sb, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => {
                self.inst_fn_set_obj(fs, param_to_arg_map)
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
                self.inst_anonymous_fn_obj(af, param_to_arg_map)
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(s)) => {
                Ok(Obj::StructAndFieldAccessObj(
                    StructAndFieldAccessObj::StructObj(self.inst_struct_obj(s, param_to_arg_map)?),
                ))
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a)) => Ok(
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(
                    self.inst_field_access(a, param_to_arg_map)?,
                )),
            ),
            Obj::InstantiatedTemplateObj(a) => Ok(Obj::InstantiatedTemplateObj(
                self.inst_instantiated_template(a, param_to_arg_map)?,
            )),
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(i)) => {
                self.inst_one_side_infinity_interval(i, param_to_arg_map)
            }
            Obj::SetFormer(SetFormer::IntervalObj(i)) => self.inst_interval(i, param_to_arg_map),
        }
    }
}
