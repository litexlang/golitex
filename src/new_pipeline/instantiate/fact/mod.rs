mod atomic;
mod compound;
mod quantified;

pub use atomic::inst_atomic_fact;
pub use compound::{inst_quantifier_free_fact, quantifier_free_fact_to_fact};
pub use quantified::inst_fact;

pub(crate) use compound::{collect_free_plain_names_in_qf_fact, inst_qf_facts};
