//! new_pipeline parse: token blocks → AST only.
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
//! 1. Name is identity (see `new_pipeline/identifier_identity.md`): no
//!    shadowing; no same-name nested binders. That doc also explains why
//!    occurrence ids were removed and what must not be broken.
//! 2. Scope is occupy only; binders and definitions are both plain String names.
//! 3. FactId may be allocated at parse; do not store facts or read ExecEnv here.
//! 4. Errors use RuntimeParseError + LineFile from TokenBlock.
//!
//! Deferred: setting-reference expand at parse; by induc binder reuse (parse_error).

mod fact;
mod fact_prop;
pub mod keywords;
mod let_stmt;
mod object;
mod param;
mod parse;
mod statements;
