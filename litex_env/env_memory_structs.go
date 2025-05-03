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

type StoredPropMemDictNode struct{ Def *ast.DefConPropStmt }

type PropMem struct {
	// 之所以是 map[string][string] 而不是 map[string]，因为虽然用户在当前的项目里，始终第一个key是""，但如果我读入了来自其他地方的包，那就是另外一个名字了
	Dict map[string]map[string]StoredPropMemDictNode
}

type StoredExistPropMemDictNode struct{ Def *ast.DefConExistPropStmt }
type ExistPropMem struct {
	Dict map[string]map[string]StoredExistPropMemDictNode
}

type StoredObjMemDictNode struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]StoredObjMemDictNode
}

type FnMem struct {
	Dict map[string]map[string]StoredFnMemDictNode
}

type StoredFnMemDictNode struct{ Def *ast.DefConFnStmt }

type StoredSpecFact struct {
	Fact *ast.SpecFactStmt
}

type StoredSpecFactInLogicExpr struct {
	Fact      *ast.SpecFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type StoredSpecMemDictNodeNode struct {
	Facts            []StoredSpecFact
	FactsINLogicExpr []StoredSpecFactInLogicExpr
}
type StoredSpecMemDictNode struct {
	PureFacts         StoredSpecMemDictNodeNode
	NotPureFacts      StoredSpecMemDictNodeNode
	ExistFacts        StoredSpecMemDictNodeNode
	NotExistFacts     StoredSpecMemDictNodeNode
	Exist_St_Facts    StoredSpecMemDictNodeNode
	NotExist_St_Facts StoredSpecMemDictNodeNode
}
type SpecFactMemDict struct {
	Dict map[string]map[string]StoredSpecMemDictNode
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

type StoredUniSpecFact struct {
	SpecFact *ast.SpecFactStmt
	// TypeEnum ast.SpecFactEnum
	// FuncParams *[]ast.Fc // 和存在Fact里的FuncFact共享slice，只要是共享，那我就用*[]，虽然确实 Fact里的 FuncFact 日后不会改变，且二者再也不相见了
	UniFact *ast.ConUniFactStmt
}

type StoredUniSpecFactUnderLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.ConUniFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type StoredUniFuncMemDictNodeNode struct {
	Facts            []StoredUniSpecFact
	FactsInLogicExpr []StoredUniSpecFactUnderLogicExpr
}

type StoredUniFuncMemDictNode struct {
	PureFacts         StoredUniFuncMemDictNodeNode
	NotPureFacts      StoredUniFuncMemDictNodeNode
	ExistFacts        StoredUniFuncMemDictNodeNode
	NotExistFacts     StoredUniFuncMemDictNodeNode
	Exist_St_Facts    StoredUniFuncMemDictNodeNode
	NotExist_St_Facts StoredUniFuncMemDictNodeNode
}

type UniFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredUniFuncMemDictNode
}
