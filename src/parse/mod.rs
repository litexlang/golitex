//! Parse: token blocks → AST only.
//!
//! Layers (dependency goes downward only):
//!   parse.rs          — statement dispatch
//!   statements/*      — Stmt
//!   fact/*            — Fact
//!   object/*          — Obj
//!   param.rs          — typed parameter lists
//!   keywords.rs       — local spellings (no legacy syntax import)
//!
//! Iron rules:
//! 1. Plain atoms carry IdentifierId (see `identifier_identity.md`):
//!    no shadowing; no same-name nested binders; letter reuse allocates a new id.
//! 2. ParseScope maps plain name → IdentifierId only.
//! 3. FactId / IdentifierId may be allocated at parse; do not store facts or read
//!    ExecEnv here.
//! 4. Errors, TokenBlock paths and AST SourceLine share CodeSource.
//!
//! `by induc n` selects a visible binder; declarations still reject shadowing.

mod fact;
mod fact_prop;
pub mod keywords;
mod let_stmt;
mod object;
mod param;
mod parse;
mod statements;

#[cfg(test)]
#[path = "../../tests/unit/parse/input_integrity.rs"]
mod input_integrity_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/nonempty_proof_bodies.rs"]
mod nonempty_proof_body_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/function_signature_scopes.rs"]
mod function_signature_scope_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/reserved_object_bindings.rs"]
mod reserved_object_binding_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/retired_product_syntax.rs"]
mod retired_product_syntax_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/retired_function_arrow.rs"]
mod retired_function_arrow_tests;

#[cfg(test)]
#[path = "../../tests/unit/parse/absolute_value_bars.rs"]
mod absolute_value_bar_tests;

pub use statements::prop_registration_shape;
