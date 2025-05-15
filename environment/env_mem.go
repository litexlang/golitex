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

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

type PropMemItem struct{ Def *ast.DefPropStmt }
type PropDefMem struct {
	Dict glob.Map2D[PropMemItem]
}

type ExistPropMemItem struct{ Def *ast.DefExistPropStmt }
type ExistPropDefMem struct {
	Dict glob.Map2D[ExistPropMemItem]
}

type ObjMemItem struct{ Def *ast.DefObjStmt }
type ObjDefMem struct {
	Dict glob.Map2D[ObjMemItem]
}

type FnMemItem struct{ Def *ast.DefFnStmt }
type FnDefMem struct {
	Dict glob.Map2D[FnMemItem]
}

type SetMemItem struct{ Def *ast.SetDefSetBuilderStmt }
type SetDefMem struct {
	Dict glob.Map2D[SetMemItem]
}

type KnownSpecFact struct {
	Fact *ast.SpecFactStmt
}

type EmitWhenSpecFactIsTrueMem struct {
	Dict glob.Map2D[[]ast.UniFactStmt] // 实际上根本不必要是 UniFact，只要保留 params (为了制作 uniMap), thenFacts (自由事实，为了未来制作 instantiated then facts) 就行
}

type SpecFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact]
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type SpecFactInLogicExprMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact_InLogicExpr]
	NotPureFacts      glob.Map2D[[]KnownSpecFact_InLogicExpr]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact_InLogicExpr]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact_InLogicExpr]
}

type KnownSpecFact_InUniSpecFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
}

type SpecFactInUniFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact_InUniSpecFact]
}

type SpecFact_InLogicExpr_InUniFact struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.UniFactStmt
	Index     []uint8
	LogicExpr *ast.LogicExprStmt
}

type SpecFact_InLogicExpr_InUniFactMem struct {
	PureFacts         glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	NotPureFacts      glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	Exist_St_Facts    glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	NotExist_St_Facts glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
}
