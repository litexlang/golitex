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

import ast "golitex/ast"

type PropMemItem struct{ Def *ast.DefPropStmt }
type PropMem struct {
	Dict map[string]map[string]PropMemItem
}

type ExistPropMemItem struct{ Def *ast.DefExistPropStmt }
type ExistPropMem struct {
	Dict map[string]map[string]ExistPropMemItem
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]ObjMemItem
}

type FnMemItem struct{ Def *ast.DefFnStmt }
type FnMem struct {
	Dict map[string]map[string]FnMemItem
}

type SetMemItem struct{ Def *ast.SetDefSetBuilderStmt }
type SetMem struct {
	Dict map[string]map[string]SetMemItem
}

type KnownSpecFact struct {
	Fact *ast.SpecFactStmt
}

type EmitWhenSpecFactIsTrueMem struct {
	Dict map[string]map[string][]ast.UniFactStmt // 实际上根本不必要是 UniFact，只要保留 params (为了制作 uniMap), thenFacts (自由事实，为了未来制作 instantiated then facts) 就行
}

type SpecFactMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact
	NotPureFacts      map[string]map[string][]KnownSpecFact
	ExistFacts        map[string]map[string][]KnownSpecFact
	NotExistFacts     map[string]map[string][]KnownSpecFact
	Exist_St_Facts    map[string]map[string][]KnownSpecFact
	NotExist_St_Facts map[string]map[string][]KnownSpecFact
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type SpecFactInLogicExprMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InLogicExpr
	NotPureFacts      map[string]map[string][]KnownSpecFact_InLogicExpr
	ExistFacts        map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExistFacts     map[string]map[string][]KnownSpecFact_InLogicExpr
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InLogicExpr
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InLogicExpr
}

type KnownSpecFact_InUniSpecFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
}

type SpecFactInUniFactMem struct {
	PureFacts         map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotPureFacts      map[string]map[string][]KnownSpecFact_InUniSpecFact
	ExistFacts        map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotExistFacts     map[string]map[string][]KnownSpecFact_InUniSpecFact
	Exist_St_Facts    map[string]map[string][]KnownSpecFact_InUniSpecFact
	NotExist_St_Facts map[string]map[string][]KnownSpecFact_InUniSpecFact
}

type SpecFact_InLogicExpr_InUniFact struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.UniFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type SpecFact_InLogicExpr_InUniFactMem struct {
	PureFacts         map[string]map[string][]SpecFact_InLogicExpr_InUniFact
	NotPureFacts      map[string]map[string][]SpecFact_InLogicExpr_InUniFact
	ExistFacts        map[string]map[string][]SpecFact_InLogicExpr_InUniFact
	NotExistFacts     map[string]map[string][]SpecFact_InLogicExpr_InUniFact
	Exist_St_Facts    map[string]map[string][]SpecFact_InLogicExpr_InUniFact
	NotExist_St_Facts map[string]map[string][]SpecFact_InLogicExpr_InUniFact
}
