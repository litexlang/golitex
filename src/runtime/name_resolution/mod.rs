mod bare_symbols;
mod free_parameters;
mod local_scopes;
mod name_generation;
mod object_resolution;
mod parameter_definition;
mod symbols;

pub use bare_symbols::BareSymbol;
pub use free_parameters::{FreeParamCollection, FreeParamTypeAndLineFile};
pub use symbols::{bare_symbol_name_reserved_error, source_binder_must_respect_bare_symbols};
