mod atomic;
mod compound;
mod quantified;

pub use compound::quantifier_free_fact_to_fact;

pub(crate) use compound::collect_free_plain_names_in_qf_fact;
