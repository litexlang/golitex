// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

type KnownSpecFact struct {
	Fact    *ast.SpecFactStmt
	EnvFact *ast.SpecFactStmt
}

type SpecFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact]
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	Index     int
	LogicExpr *ast.OrStmt
	EnvFact   *ast.SpecFactStmt
}

func NewKnownSpecFact_InLogicExpr(specFact *ast.SpecFactStmt, index int, logicExpr *ast.OrStmt, envFact *ast.SpecFactStmt) *KnownSpecFact_InLogicExpr {
	return &KnownSpecFact_InLogicExpr{specFact, index, logicExpr, envFact}
}

type SpecFactInLogicExprMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact_InLogicExpr]
	NotPureFacts      glob.Map2D[[]KnownSpecFact_InLogicExpr]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact_InLogicExpr]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact_InLogicExpr]
}

type KnownSpecFact_InUniFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
	EnvFact  *ast.SpecFactStmt
}

type SpecFactInUniFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact_InUniFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact_InUniFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact_InUniFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact_InUniFact]
}

type SpecFact_InLogicExpr_InUniFact struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.UniFactStmt
	Index     int
	LogicExpr *ast.OrStmt
	EnvFact   *ast.SpecFactStmt
}

func NewSpecFact_InLogicExpr_InUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt, index int, logicExpr *ast.OrStmt, envFact *ast.SpecFactStmt) *SpecFact_InLogicExpr_InUniFact {
	return &SpecFact_InLogicExpr_InUniFact{specFact, uniFact, index, logicExpr, envFact}
}

type SpecFact_InLogicExpr_InUniFactMem struct {
	PureFacts         glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	NotPureFacts      glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	Exist_St_Facts    glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
	NotExist_St_Facts glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]
}

func newSpecFactMem() *SpecFactMem {
	return &SpecFactMem{
		PureFacts:         make(glob.Map2D[[]KnownSpecFact]),
		NotPureFacts:      make(glob.Map2D[[]KnownSpecFact]),
		Exist_St_Facts:    make(glob.Map2D[[]KnownSpecFact]),
		NotExist_St_Facts: make(glob.Map2D[[]KnownSpecFact]),
	}
}

func newSpecFactInLogicExprMem() *SpecFactInLogicExprMem {
	return &SpecFactInLogicExprMem{
		PureFacts:         make(glob.Map2D[[]KnownSpecFact_InLogicExpr]),
		NotPureFacts:      make(glob.Map2D[[]KnownSpecFact_InLogicExpr]),
		Exist_St_Facts:    make(glob.Map2D[[]KnownSpecFact_InLogicExpr]),
		NotExist_St_Facts: make(glob.Map2D[[]KnownSpecFact_InLogicExpr]),
	}
}

func newSpecFactInUniFact() *SpecFactInUniFactMem {
	return &SpecFactInUniFactMem{
		PureFacts:         make(glob.Map2D[[]KnownSpecFact_InUniFact]),
		NotPureFacts:      make(glob.Map2D[[]KnownSpecFact_InUniFact]),
		Exist_St_Facts:    make(glob.Map2D[[]KnownSpecFact_InUniFact]),
		NotExist_St_Facts: make(glob.Map2D[[]KnownSpecFact_InUniFact]),
	}
}

func NewKnownSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		NotPureFacts:      make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		Exist_St_Facts:    make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
		NotExist_St_Facts: make(glob.Map2D[[]SpecFact_InLogicExpr_InUniFact]),
	}
}
