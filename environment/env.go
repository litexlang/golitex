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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

type shared_ptr_to_slice_of_fc = *[]ast.Fc

type PropDefMem map[string]ast.DefPropStmt

type ExistPropDefMem map[string]ast.DefExistPropStmt

type FnTemplateDefMem map[string]ast.FnTemplateDefStmt

type ObjDefMem map[string]ast.FnTemplate_Or_DefObjStmtInterface // 因为很多的obj会共享一个def obj. 可能是 nil

type FnInFnTMem map[string][]FnInFnTMemItem

type FnInFnTMemItem struct {
	// AsFcFn      *ast.FcFn // 可能是 fn(R)R 这种，或者 TName(params) 这样，或者是nil（比如 defFnStmt 声明出来的）
	AsFnTStruct *ast.FnTStruct
}

type HaveSetFnDefMem map[string]ast.HaveSetFnStmt

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
}

// 因为 in 类型的事实很多，考虑把fcString为key保留一个map，记录它在什么集合里。比如 a $in N 就保存成 key:a values:[]{N}
type Env struct {
	Parent                 *Env
	Msgs                   glob.Msgs
	ObjDefMem              ObjDefMem
	PropDefMem             PropDefMem
	FnTemplateDefMem       FnTemplateDefMem
	ExistPropDefMem        ExistPropDefMem
	KnownFactsStruct       KnownFactsStruct
	FnInFnTemplateFactsMem FnInFnTMem
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
		Msgs:                   glob.Msgs{},
		ObjDefMem:              make(ObjDefMem),
		PropDefMem:             make(PropDefMem),
		FnTemplateDefMem:       make(FnTemplateDefMem),
		FnInFnTemplateFactsMem: make(FnInFnTMem),
		ExistPropDefMem:        make(ExistPropDefMem),
		KnownFactsStruct:       makeKnownFactsStruct(),
		EqualMem:               make(map[string]shared_ptr_to_slice_of_fc),
		KnownFactInMatchEnv:    make(map[string]KnownFactsStruct),
		EnumFacts:              make(map[string][]ast.Fc),
		HaveSetFnDefMem:        make(HaveSetFnDefMem),
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
