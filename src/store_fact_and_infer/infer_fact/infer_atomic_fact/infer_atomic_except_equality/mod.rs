//! Infer for stored atomics that are not EqualFact.

pub mod infer_in_fact;
pub mod infer_normal_atomic_fact;
pub mod membership_cart_interval;
pub mod membership_fn;
pub mod membership_index_family;
pub mod membership_list_set_ops;
mod membership_preimage;
pub mod membership_signed_standard_set;
pub mod order_sign;
pub mod store_builtin_definition_consequences;
pub mod subset;
pub mod superset;

mod infer_bijective_fact;
mod infer_coprime_fact;
mod infer_dvd_fact;
mod infer_injective_fact;
mod infer_is_choice_function_for_fact;
mod infer_prime_fact;
mod infer_proper_subset_fact;
mod infer_proper_superset_fact;
mod infer_surjective_fact;
