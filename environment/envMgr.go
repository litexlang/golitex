// Copyright Jiachen Shen.
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

import ast "golitex/ast"

type shared_ptr_to_slice_of_obj = *[]ast.Obj
type PropDefMem map[string]ast.DefPropStmt

// type ExistPropDefMem map[string]ast.DefExistPropStmt
type FnTemplateDefMem map[string]ast.DefFnSetStmt
type AtomObjDefMem map[string]*ast.DefLetStmt // 因为很多的obj会共享一个def obj. 可能是 nil
type FnInFnTMem map[string][]FnInFnTMemItem
type PropCommutativeCase struct {
	TruePureIsCommutative  bool
	FalsePureIsCommutative bool
}

type FnInFnTMemItem struct {
	AsFnTStruct *ast.AnonymousFn
}

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
	SpecFactInImplyTemplateMem        SpecFactInImplyTemplateMem
}

type DefinedStuff[T any] struct {
	Defined  T
	EnvDepth int
}

func NewDefinedStuff[T any](defined T, envDepth int) DefinedStuff[T] {
	return DefinedStuff[T]{Defined: defined, EnvDepth: envDepth}
}

type EnvMgr struct {
	EnvPkgMgr *EnvPkgMgr
	EnvSlice  []EnvMemory

	AllDefinedAtomObjNames map[string]DefinedStuff[struct{}]
	AllDefinedPropNames    map[string]DefinedStuff[*ast.DefPropStmt]
	// AllDefinedExistPropNames map[string]*ast.DefExistPropStmt
	AllDefinedFnSetNames map[string]DefinedStuff[*ast.DefFnSetStmt]
	AllDefinedAlgoNames  map[string]DefinedStuff[*ast.DefAlgoStmt]
	// AllDefinedProveAlgoNames map[string]DefinedStuff[*ast.DefProveAlgoStmt]
}

type EnvMemory struct {
	// definition memory
	AtomObjDefMem    map[string]struct{}
	PropDefMem       map[string]struct{}
	FnTemplateDefMem map[string]struct{}
	ExistPropDefMem  map[string]struct{}
	AlgoDefMem       map[string]struct{}
	// DefProveAlgoMem  map[string]struct{}

	// facts memory
	EqualMem                 map[string]shared_ptr_to_slice_of_obj
	KnownFactsStruct         KnownFactsStruct
	SymbolSimplifiedValueMem map[string]ast.Obj

	// transitive prop and commutative prop
	TransitivePropMem  map[string]map[string][]ast.Obj
	CommutativePropMem map[string]*PropCommutativeCase

	// function template facts
	FnInFnTemplateFactsMem FnInFnTMem
}

func NewEnvMemory() *EnvMemory {
	return &EnvMemory{
		AtomObjDefMem:    make(map[string]struct{}),
		PropDefMem:       make(map[string]struct{}),
		FnTemplateDefMem: make(map[string]struct{}),
		ExistPropDefMem:  make(map[string]struct{}),
		AlgoDefMem:       make(map[string]struct{}),
		// DefProveAlgoMem:  make(map[string]struct{}),

		EqualMem:                 make(map[string]shared_ptr_to_slice_of_obj),
		KnownFactsStruct:         makeKnownFactsStruct(),
		SymbolSimplifiedValueMem: make(map[string]ast.Obj),

		TransitivePropMem:  make(map[string]map[string][]ast.Obj),
		CommutativePropMem: make(map[string]*PropCommutativeCase),

		FnInFnTemplateFactsMem: make(FnInFnTMem),
	}
}

func NewEnvMgr(pkgMgr *EnvPkgMgr, envMemory []EnvMemory, allDefinedAtomObjNames map[string]DefinedStuff[struct{}], allDefinedPropNames map[string]DefinedStuff[*ast.DefPropStmt], allDefinedFnTemplateNames map[string]DefinedStuff[*ast.DefFnSetStmt], allDefinedAlgoNames map[string]DefinedStuff[*ast.DefAlgoStmt]) *EnvMgr {
	return &EnvMgr{
		AllDefinedAtomObjNames: allDefinedAtomObjNames,
		AllDefinedPropNames:    allDefinedPropNames,
		// AllDefinedExistPropNames: allDefinedExistPropNames,
		AllDefinedFnSetNames: allDefinedFnTemplateNames,
		AllDefinedAlgoNames:  allDefinedAlgoNames,
		// AllDefinedProveAlgoNames: allDefinedProveAlgoNames,
		EnvPkgMgr: pkgMgr,
		EnvSlice:  envMemory,
	}
}

func (envMgr *EnvMgr) NewEnv() *EnvMgr {
	envMgr.EnvSlice = append(envMgr.EnvSlice, *NewEnvMemory())
	return envMgr
}

// func (envMgr *EnvMgr) DeleteEnvUntilBuiltin() {
// 	for len(envMgr.EnvSlice) > 1 {
// 		envMgr.DeleteEnv()
// 	}
// }

func (envMgr *EnvMgr) DeleteEnv() {
	// 把 当前的 def 从 all defined 里删了，不删最后一个，因为最后一个是最顶层的
	for k := range envMgr.CurEnv().AtomObjDefMem {
		delete(envMgr.AllDefinedAtomObjNames, k)
	}
	for k := range envMgr.CurEnv().PropDefMem {
		delete(envMgr.AllDefinedPropNames, k)
	}
	// for k := range envMgr.CurEnv().ExistPropDefMem {
	// 	delete(envMgr.AllDefinedExistPropNames, k)
	// }
	for k := range envMgr.CurEnv().FnTemplateDefMem {
		delete(envMgr.AllDefinedFnSetNames, k)
	}
	for k := range envMgr.CurEnv().AlgoDefMem {
		delete(envMgr.AllDefinedAlgoNames, k)
	}
	// for k := range envMgr.CurEnv().DefProveAlgoMem {
	// 	delete(envMgr.AllDefinedProveAlgoNames, k)
	// }

	envMgr.EnvSlice = envMgr.EnvSlice[:len(envMgr.EnvSlice)-1]
}

func makeKnownFactsStruct() KnownFactsStruct {
	return KnownFactsStruct{
		SpecFactMem:                       *newSpecFactMem(),
		SpecFactInLogicExprMem:            *newSpecFactInLogicExprMem(),
		SpecFactInUniFactMem:              *newSpecFactInUniFact(),
		SpecFact_InLogicExpr_InUniFactMem: *newSpecFact_InLogicExpr_InUniFactMem(),
		SpecFactInImplyTemplateMem:        *newSpecFactInImplyTemplateMem(),
	}
}

func newSpecFact_InLogicExpr_InUniFactMem() *SpecFact_InLogicExpr_InUniFactMem {
	return &SpecFact_InLogicExpr_InUniFactMem{
		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
	}
}

func NewCommutativePropMemItemStruct() *PropCommutativeCase {
	return &PropCommutativeCase{
		TruePureIsCommutative:  false,
		FalsePureIsCommutative: false,
	}
}

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

type SpecFactInImplyTemplateMem struct {
	PureFacts         map[string][]KnownSpecFact_InImplyTemplate
	NotPureFacts      map[string][]KnownSpecFact_InImplyTemplate
	Exist_St_Facts    map[string][]KnownSpecFact_InImplyTemplate
	NotExist_St_Facts map[string][]KnownSpecFact_InImplyTemplate
}

func newSpecFactInImplyTemplateMem() *SpecFactInImplyTemplateMem {
	return &SpecFactInImplyTemplateMem{
		PureFacts:         make(map[string][]KnownSpecFact_InImplyTemplate),
		NotPureFacts:      make(map[string][]KnownSpecFact_InImplyTemplate),
		Exist_St_Facts:    make(map[string][]KnownSpecFact_InImplyTemplate),
		NotExist_St_Facts: make(map[string][]KnownSpecFact_InImplyTemplate),
	}
}

type KnownSpecFact_InImplyTemplate struct {
	Spec_orFact   ast.Spec_OrFact
	ImplyTemplate *ast.InferTemplateStmt
}

func NewKnownSpecFact_InImplyTemplate(known ast.Spec_OrFact, implyTemplate *ast.InferTemplateStmt) KnownSpecFact_InImplyTemplate {
	return KnownSpecFact_InImplyTemplate{known, implyTemplate}
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

func (envMgr *EnvMgr) CurEnvDepth() int {
	return len(envMgr.EnvSlice) - 1
}

func (envMgr *EnvMgr) CurEnv() *EnvMemory {
	return &envMgr.EnvSlice[len(envMgr.EnvSlice)-1]
}

func NewEmptyEnvMgr(envPkgMgr *EnvPkgMgr) *EnvMgr {
	return NewEnvMgr(envPkgMgr, []EnvMemory{*NewEnvMemory()}, make(map[string]DefinedStuff[struct{}]), make(map[string]DefinedStuff[*ast.DefPropStmt]), make(map[string]DefinedStuff[*ast.DefFnSetStmt]), make(map[string]DefinedStuff[*ast.DefAlgoStmt]))
}
