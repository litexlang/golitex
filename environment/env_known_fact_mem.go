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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	ast "golitex/ast"
)

type SpecFactMem struct {
	PureFacts         map[string][]ast.SpecFactStmt
	NotPureFacts      map[string][]ast.SpecFactStmt
	Exist_St_Facts    map[string][]ast.SpecFactStmt
	NotExist_St_Facts map[string][]ast.SpecFactStmt
}

type KnownSpecFact_InLogicExpr struct {
	SpecFact  *ast.SpecFactStmt
	Index     int
	LogicExpr *ast.OrStmt
}

func NewKnownSpecFact_InLogicExpr(specFact *ast.SpecFactStmt, index int, logicExpr *ast.OrStmt) *KnownSpecFact_InLogicExpr {
	return &KnownSpecFact_InLogicExpr{specFact, index, logicExpr}
}

type SpecFactInLogicExprMem struct {
	PureFacts         map[string][]KnownSpecFact_InLogicExpr
	NotPureFacts      map[string][]KnownSpecFact_InLogicExpr
	Exist_St_Facts    map[string][]KnownSpecFact_InLogicExpr
	NotExist_St_Facts map[string][]KnownSpecFact_InLogicExpr
}

type KnownSpecFact_InUniFact struct {
	SpecFact *ast.SpecFactStmt
	UniFact  *ast.UniFactStmt
}

func MakeKnownSpecFact_InUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) KnownSpecFact_InUniFact {
	return KnownSpecFact_InUniFact{specFact, uniFact}
}

type SpecFactInUniFactMem struct {
	PureFacts         map[string][]KnownSpecFact_InUniFact
	NotPureFacts      map[string][]KnownSpecFact_InUniFact
	Exist_St_Facts    map[string][]KnownSpecFact_InUniFact
	NotExist_St_Facts map[string][]KnownSpecFact_InUniFact
}

type SpecFact_InLogicExpr_InUniFact struct {
	SpecFact  *ast.SpecFactStmt
	UniFact   *ast.UniFactStmt
	Index     int
	LogicExpr *ast.OrStmt
}

func NewSpecFact_InLogicExpr_InUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt, index int, logicExpr *ast.OrStmt) *SpecFact_InLogicExpr_InUniFact {
	return &SpecFact_InLogicExpr_InUniFact{specFact, uniFact, index, logicExpr}
}

type SpecFact_InLogicExpr_InUniFactMem struct {
	PureFacts         map[string][]SpecFact_InLogicExpr_InUniFact
	NotPureFacts      map[string][]SpecFact_InLogicExpr_InUniFact
	Exist_St_Facts    map[string][]SpecFact_InLogicExpr_InUniFact
	NotExist_St_Facts map[string][]SpecFact_InLogicExpr_InUniFact
}

func newSpecFactMem() *SpecFactMem {
	return &SpecFactMem{
		PureFacts:         make(map[string][]ast.SpecFactStmt),
		NotPureFacts:      make(map[string][]ast.SpecFactStmt),
		Exist_St_Facts:    make(map[string][]ast.SpecFactStmt),
		NotExist_St_Facts: make(map[string][]ast.SpecFactStmt),
	}
}

func newSpecFactInLogicExprMem() *SpecFactInLogicExprMem {
	return &SpecFactInLogicExprMem{
		PureFacts:         make(map[string][]KnownSpecFact_InLogicExpr),
		NotPureFacts:      make(map[string][]KnownSpecFact_InLogicExpr),
		Exist_St_Facts:    make(map[string][]KnownSpecFact_InLogicExpr),
		NotExist_St_Facts: make(map[string][]KnownSpecFact_InLogicExpr),
	}
}

func newSpecFactInUniFact() *SpecFactInUniFactMem {
	return &SpecFactInUniFactMem{
		PureFacts:         make(map[string][]KnownSpecFact_InUniFact),
		NotPureFacts:      make(map[string][]KnownSpecFact_InUniFact),
		Exist_St_Facts:    make(map[string][]KnownSpecFact_InUniFact),
		NotExist_St_Facts: make(map[string][]KnownSpecFact_InUniFact),
	}
}

func NewKnownSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
	}
}
