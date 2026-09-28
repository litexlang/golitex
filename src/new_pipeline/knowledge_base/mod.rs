//! Persist and restore imported-module products (fingerprint, serialize, load).
//!
//! On-disk artifacts live under each module's `__litex_knowledge_base__/`.
//! See `README.md` in this package.

mod def_abstract_prop_codec;
mod def_prop_codec;
mod def_thm_codec;
mod json_mini;
mod stored_identifier_codec;

pub use def_abstract_prop_codec::{
    load_def_abstract_prop, read_def_abstract_prop, store_def_abstract_prop,
    write_def_abstract_prop,
};
pub use def_prop_codec::{
    load_def_prop, read_def_prop, store_def_prop, write_def_prop, KbCodecError,
};
pub use def_thm_codec::{load_def_thm, read_def_thm, store_def_thm, write_def_thm};
pub use stored_identifier_codec::{
    load_stored_identifier, read_stored_identifier, store_stored_identifier,
    write_stored_identifier,
};

#[cfg(test)]
#[path = "../../../tests/unit/new_pipeline/knowledge_base/mod.rs"]
mod unit_tests;
