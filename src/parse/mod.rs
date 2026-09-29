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
//! 4. Errors use RuntimeParseError + TokenBlock path; AST uses SourceLine (CodeSource).
//!
//! Deferred: by induc binder reuse (parse_error).

mod fact;
mod fact_prop;
pub mod keywords;
mod let_stmt;
mod object;
mod param;
mod parse;
mod statements;

pub use statements::prop_registration_shape;
