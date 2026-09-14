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
//! 1. Names are String; Identifier / IdentifierWithMod carry global IdentifierId stamped at parse.
//! 2. Scope is occupy only (no shadowing); identifiers stay Identifier (no Bound rewrite).
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
