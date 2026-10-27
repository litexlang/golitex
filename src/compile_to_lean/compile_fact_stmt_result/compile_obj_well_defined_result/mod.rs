mod compile_abs;
mod compile_arithmetic;
mod compile_closed_range;
mod compile_finite_function;
mod compile_finite_seq;
mod compile_function_call;
mod compile_function_space;
pub(in crate::compile_to_lean) mod compile_min_max;
mod compile_numeric_observation;
pub(in crate::compile_to_lean) use compile_min_max::min_max_arguments;
pub(in crate::compile_to_lean) mod compile_factorial;
pub(in crate::compile_to_lean) mod compile_gcd_lcm;
pub(in crate::compile_to_lean) mod compile_integer_division;
mod compile_obj_well_defined_result;
mod compile_product_shape;
mod compile_returned_array_call;
mod compile_returned_cart_call;
mod compile_returned_fn_call;
pub(in crate::compile_to_lean) mod compile_rounding;
mod compile_set_former;
mod compile_set_operator;
mod compile_sign;
mod compile_sqrt;

pub(in crate::compile_to_lean) use compile_finite_function::{
    finite_call_parts, validate_finite_signature,
};

mod compile_finite_aggregate;
mod compile_finite_fold;
mod compile_finite_set_stat;
mod compile_range_aggregate;
mod compile_range_fold;
mod compile_real_interval;
mod compile_seq;

mod compile_exp_log;

pub(in crate::compile_to_lean) mod compile_trig;

pub(in crate::compile_to_lean) mod compile_complex;

pub(in crate::compile_to_lean) mod compile_hyperbolic;

mod compile_matrix_set;

mod compile_matrix_operator;

mod compile_tuple_standard_function_member;
