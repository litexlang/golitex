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

import ast "golitex/litex_ast"

type KnownSpecFact struct {
	Fact *ast.SpecFactStmt
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type EnumSpecFactMem struct {
	Facts            []KnownSpecFact
	FactsINLogicExpr []KnownSpecFact_InLogicExpr
}

type KnownSpecFact_InUniSpecFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
}

type KnownSpecFact_InLogicExpr_InUniFact struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.UniFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

// type EnumUniFactMem struct {
// 	Facts            []KnownSpecFact_InUniSpecFact
// 	ParentLogicFacts []KnownSpecFact_InLogicExpr_InUniFact
// }

// type UniFactMemItem struct {
// 	PureFacts         EnumUniFactMem
// 	NotPureFacts      EnumUniFactMem
// 	ExistFacts        EnumUniFactMem
// 	NotExistFacts     EnumUniFactMem
// 	Exist_St_Facts    EnumUniFactMem
// 	NotExist_St_Facts EnumUniFactMem
// }

// type UniFactMem struct {
// 	SpecFactsDict map[string]map[string]UniFactMemItem
// }
