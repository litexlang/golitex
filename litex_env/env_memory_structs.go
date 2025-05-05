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

type PropMemItem struct{ Def *ast.DefConPropStmt }
type PropMem struct {
	Dict map[string]map[string]PropMemItem
}

type ExistPropMemItem struct{ Def *ast.DefConExistPropStmt }
type ExistPropMem struct {
	Dict map[string]map[string]ExistPropMemItem
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]ObjMemItem
}

type FnMemItem struct{ Def *ast.DefConFnStmt }
type FnMem struct {
	Dict map[string]map[string]FnMemItem
}

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

// 有很多的 spec fact 是没有 exist的，所以应该在1 specFactmem 里就分好 enum，而不是在同名specfact下面分
// type SpecFactMemItem struct {
// 	PureFacts         EnumSpecFactMem
// 	NotPureFacts      EnumSpecFactMem
// 	ExistFacts        EnumSpecFactMem
// 	NotExistFacts     EnumSpecFactMem
// 	Exist_St_Facts    EnumSpecFactMem
// 	NotExist_St_Facts EnumSpecFactMem
// }
// type SpecFactMem struct {
// 	Dict map[string]map[string]SpecFactMemItem
// }

type SpecFactMem struct {
	// first map correspond to pkgName, second map correspond to propName
	PureFacts         map[string]map[string]EnumSpecFactMem
	NotPureFacts      map[string]map[string]EnumSpecFactMem
	ExistFacts        map[string]map[string]EnumSpecFactMem
	NotExistFacts     map[string]map[string]EnumSpecFactMem
	Exist_St_Facts    map[string]map[string]EnumSpecFactMem
	NotExist_St_Facts map[string]map[string]EnumSpecFactMem
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

type EnumUniFactMem struct {
	Facts            []KnownSpecFact_InUniSpecFact
	ParentLogicFacts []KnownSpecFact_InLogicExpr_InUniFact
}

type UniFactMemItem struct {
	PureFacts         EnumUniFactMem
	NotPureFacts      EnumUniFactMem
	ExistFacts        EnumUniFactMem
	NotExistFacts     EnumUniFactMem
	Exist_St_Facts    EnumUniFactMem
	NotExist_St_Facts EnumUniFactMem
}

type UniFactMem struct {
	SpecFactsDict map[string]map[string]UniFactMemItem
}

// type StoredCondSpecFact struct {
// 	SpecFact *ast.SpecFactStmt
// 	Fact     *ast.CondFactStmt
// }

// type StoredCondFuncMemDictNodeNode struct {
// 	Facts            []StoredCondSpecFact
// 	FactsInLogicExpr []StoredCondSpecFactUnderLogicExpr
// }

// type StoredCondSpecFactUnderLogicExpr struct {
// 	SpecFact  *ast.SpecFactStmt
// 	CondFact  *ast.CondFactStmt
// 	Index     []uint8
// 	LogicExpr *ast.LogicExprStmt
// }

// type StoredCondFuncMemDictNode struct {
// 	PureFacts         StoredCondFuncMemDictNodeNode
// 	NotPureFacts      StoredCondFuncMemDictNodeNode
// 	ExistFacts        StoredCondFuncMemDictNodeNode
// 	NotExistFacts     StoredCondFuncMemDictNodeNode
// 	Exist_St_Facts    StoredCondFuncMemDictNodeNode
// 	NotExist_St_Facts StoredCondFuncMemDictNodeNode
// }

// type CondFactMemDict struct {
// 	SpecFactsDict map[string]map[string]StoredCondFuncMemDictNode
// }
