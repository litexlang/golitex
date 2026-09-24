//! Persist and restore imported-module products (fingerprint, serialize, load).
//!
//! On-disk artifacts live under each module's `__litex_knowledge_base__/`.
//! See `README.md` in this package.

mod def_prop_codec;
mod json_mini;

pub use def_prop_codec::{
    load_def_prop, read_def_prop, store_def_prop, write_def_prop, KbCodecError,
};

#[cfg(test)]
#[path = "../../../tests/unit/new_pipeline/knowledge_base/mod.rs"]
mod unit_tests;
