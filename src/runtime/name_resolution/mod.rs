mod bare_symbols;
mod free_parameters;
mod local_scopes;
mod name_generation;
mod object_resolution;
mod parameter_definition;
mod symbols;
mod transparent_definitions;

pub use bare_symbols::BareSymbol;
pub use free_parameters::{FreeParamCollection, FreeParamTypeAndLineFile};
pub use symbols::bare_symbol_name_reserved_error;
pub use transparent_definitions::TransparentObjectDefinitionUse;
