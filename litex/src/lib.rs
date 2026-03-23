// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

//! Litex kernel library (parser, runtime, verify).

pub mod calculate_and_simplify_rational_expression;
pub mod common;
pub mod environment;
pub mod error;
pub mod execute;
pub mod fact;
pub mod infer;
pub mod module_manager;
pub mod obj;
pub mod parse;
pub mod pipeline;
pub mod result;
pub mod runtime;
pub mod stmt;
pub mod verify;
