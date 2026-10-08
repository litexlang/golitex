//! Infer for stored atomics that are not EqualFact.

pub mod expand_definition;
pub mod infer_atomic_except_equality;
pub mod membership_cart_interval;
pub mod membership_fn;
mod membership_preimage;
pub mod membership_index_family;
pub mod membership_list_set_ops;
pub mod membership_projection;
pub mod membership_signed_standard_set;
pub mod subset;
pub mod superset;
pub mod order_sign;
