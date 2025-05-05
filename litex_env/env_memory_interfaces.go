// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_env

// Below are the implementations of FactMem, SamePropFacts, KnownSpecFacts

// // SpecFact memory
// type SpecFactMem2 struct {
// 	PureFacts         SpecMemField
// 	NotPureFacts      SpecMemField
// 	ExistFacts        SpecMemField
// 	NotExistFacts     SpecMemField
// 	Exist_St_Facts    SpecMemField
// 	NotExist_St_Facts SpecMemField
// }

// type KnownSpecFacts []KnownSpecFact

// func (facts KnownSpecFacts) NewFact(stmt *ast.SpecFactStmt) error {
// 	facts = append(facts, KnownSpecFact{stmt})
// 	return nil
// }

// type SpecMemField map[string]map[string]KnownSpecFacts

// // Spec Fact in Logic Expr memory

// type SpecFactInLogicExprMem2 struct {
// 	PureFacts         SpecFactInLogicExprMemField
// 	NotPureFacts      SpecFactInLogicExprMemField
// 	ExistFacts        SpecFactInLogicExprMemField
// 	NotExistFacts     SpecFactInLogicExprMemField
// 	Exist_St_Facts    SpecFactInLogicExprMemField
// 	NotExist_St_Facts SpecFactInLogicExprMemField
// }

// type KnownSpecFactInLogicExprs []KnownSpecFact_InLogicExpr

// func (facts KnownSpecFactInLogicExprs) NewFact(stmt *ast.SpecFactStmt) KnownSpecFactInLogicExprs {
// 	return facts
// }

// type SpecFactInLogicExprMemField map[string]map[string]KnownSpecFactInLogicExprs
