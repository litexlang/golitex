mod compile_abs;
mod compile_arithmetic;
mod compile_closed_range;
mod compile_finite_function;
mod compile_function_call;
mod compile_function_space;
mod compile_numeric_observation;
mod compile_obj_well_defined_result;
mod compile_product_shape;
mod compile_returned_cart_call;
mod compile_set_former;
mod compile_set_operator;
mod compile_sqrt;

pub(in crate::compile_to_lean) use compile_finite_function::{
    finite_call_parts, validate_finite_signature,
};
