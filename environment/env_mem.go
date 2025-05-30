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

type KnownSpecFact struct {
	Fact    *ast.SpecFactStmt
	EnvFact *ast.SupposePropMatchStmt
}

type SpecFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact]
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact *ast.SpecFactStmt
	// Index    []uint8
	// LogicExpr *ast.LogicExprStmt
	LogicExpr *ast.OrStmt
	EnvFact   *ast.SupposePropMatchStmt
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
	EnvFact  *ast.SupposePropMatchStmt
}

type SpecFactInUniFactMem struct {
	PureFacts         glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	NotPureFacts      glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	Exist_St_Facts    glob.Map2D[[]KnownSpecFact_InUniSpecFact]
	NotExist_St_Facts glob.Map2D[[]KnownSpecFact_InUniSpecFact]
}

type SpecFact_InLogicExpr_InUniFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
	// Index    []uint8
	// LogicExpr *ast.LogicExprStmt
	LogicExpr *ast.OrStmt
	EnvFact   *ast.SupposePropMatchStmt
}

func NewSpecFact_InLogicExpr_InUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt, logicExpr *ast.OrStmt, envFact *ast.SupposePropMatchStmt) *SpecFact_InLogicExpr_InUniFact {
	return &SpecFact_InLogicExpr_InUniFact{specFact, uniFact, logicExpr, envFact}
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
		PureFacts:         make(glob.Map2D[[]KnownSpecFact_InUniSpecFact]),
		NotPureFacts:      make(glob.Map2D[[]KnownSpecFact_InUniSpecFact]),
		Exist_St_Facts:    make(glob.Map2D[[]KnownSpecFact_InUniSpecFact]),
		NotExist_St_Facts: make(glob.Map2D[[]KnownSpecFact_InUniSpecFact]),
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
