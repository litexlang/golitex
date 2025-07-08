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

type shared_ptr_to_slice_of_fc = *[]ast.Fc

// type MatchProp = ast.SpecFactStmt

type PropDefMem map[string]ast.DefPropStmt

type ExistPropDefMem map[string]ast.DefExistPropStmt

type FnTemplateDefMem map[string]ast.DefFnTemplateStmt

// 我暂时不清楚 map[string]struct{} 有没有问题，我暂时用不到def obj 相关的任何的东西
type ObjDefMem map[string]ast.FnTemplate_Or_DefObjStmtInterface // 因为很多的obj会共享一个def obj

type FnInFnTemplateFactsMem map[string][]*ast.FnTemplateStmt

type HaveSetFnDefMem map[string]ast.HaveSetFnStmt

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
}

type Env struct {
	Parent                 *Env
	Msgs                   []string
	ObjDefMem              ObjDefMem
	PropDefMem             PropDefMem
	FnTemplateDefMem       FnTemplateDefMem
	ExistPropDefMem        ExistPropDefMem
	KnownFactsStruct       KnownFactsStruct
	FnInFnTemplateFactsMem FnInFnTemplateFactsMem
	KnownFactInMatchEnv    map[string]KnownFactsStruct
	EqualMem               map[string]shared_ptr_to_slice_of_fc
	EnumFacts              map[string][]ast.Fc
	HaveSetFnDefMem        HaveSetFnDefMem
}

func (env *Env) GetUpMostEnv() *Env {
	if env.Parent == nil {
		return env
	}
	return env.Parent.GetUpMostEnv()
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent:                 parent,
		Msgs:                   []string{},
		ObjDefMem:              make(ObjDefMem),
		PropDefMem:             make(PropDefMem),
		FnInFnTemplateFactsMem: make(FnInFnTemplateFactsMem),
		FnTemplateDefMem:       make(FnTemplateDefMem),
		ExistPropDefMem:        make(ExistPropDefMem),
		KnownFactsStruct:       makeKnownFactsStruct(),
		EqualMem:               make(map[string]shared_ptr_to_slice_of_fc),
		// KnownFactInMatchEnv:    make(glob.Map2D[KnownFactsStruct]),
		KnownFactInMatchEnv: make(map[string]KnownFactsStruct),
		// CurMatchProp:        curMatchEnv,
		EnumFacts:       make(map[string][]ast.Fc),
		HaveSetFnDefMem: make(HaveSetFnDefMem),
	}
	return env
}

func makeKnownFactsStruct() KnownFactsStruct {
	return KnownFactsStruct{
		SpecFactMem:                       *newSpecFactMem(),
		SpecFactInLogicExprMem:            *newSpecFactInLogicExprMem(),
		SpecFactInUniFactMem:              *newSpecFactInUniFact(),
		SpecFact_InLogicExpr_InUniFactMem: *newSpecFact_InLogicExpr_InUniFactMem(),
	}
}
