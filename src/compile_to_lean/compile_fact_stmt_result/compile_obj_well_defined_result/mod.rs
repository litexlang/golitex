mod compile_abs;
mod compile_arithmetic;
mod compile_closed_range;
mod compile_finite_function;
mod compile_function_call;
mod compile_function_space;
mod compile_numeric_observation;
mod compile_obj_well_defined_result;
mod compile_product_shape;
mod compile_set_former;
mod compile_set_operator;

pub(in crate::compile_to_lean) use compile_finite_function::validate_finite_signature;
