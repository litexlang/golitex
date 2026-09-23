//! Infer for stored atomics that are not EqualFact.

pub mod expand_definition;
pub mod infer_atomic_except_equality;
pub mod is_cart;
pub mod membership_cart_interval;
pub mod membership_list_set_ops;
pub mod membership_projection;
pub mod membership_standard_set;
pub mod numeric_order_sign;
pub mod subset;
pub mod superset;
