//! Infer for stored EqualFact (`a = b`).

mod helper;
pub mod infer_equal_fact;
mod infer_equal_fact_additive_cancellation;
mod infer_equal_fact_division_cancellation;
mod infer_equal_fact_nonzero_factor_cancellation;
mod infer_equal_fact_subtractive_cancellation;
pub mod positive_real_power;
