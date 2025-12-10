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

type shared_ptr_to_slice_of_obj = *[]ast.Obj

type PropDefMem map[string]ast.DefPropStmt

type ExistPropDefMem map[string]ast.DefExistPropStmt

type FnTemplateDefMem map[string]ast.FnTemplateDefStmt

type ObjDefMem map[string]ast.FnTemplate_Or_DefObjStmtInterface // 因为很多的obj会共享一个def obj. 可能是 nil

type FnInFnTMem map[string][]FnInFnTMemItem

type FnInFnTMemItem struct {
	AsFnTStruct *ast.FnTStruct
}

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
}

// 因为 in 类型的事实很多，考虑把objString为key保留一个map，记录它在什么集合里。比如 a $in N 就保存成 key:a values:[]{N}
type Env struct {
	Parent *Env

	ObjDefMem        ObjDefMem
	PropDefMem       PropDefMem
	FnTemplateDefMem FnTemplateDefMem
	ExistPropDefMem  ExistPropDefMem

	KnownFactsStruct KnownFactsStruct

	FnInFnTemplateFactsMem FnInFnTMem

	EqualMem map[string]shared_ptr_to_slice_of_obj

	// EnumFacts map[string][]ast.Obj

	// IntensionalSetMem map[string]ast.IntensionalSetStmt

	SymbolSimplifiedValueMem map[string]ast.Obj

	TransitivePropMem  map[string]map[string][]ast.Obj
	CommutativePropMem map[string]*PropCommutativeCase

	AlgoDefMem map[string]*ast.DefAlgoStmt

	DefProveAlgoMem map[string]*ast.DefProveAlgoStmt

	PackageManager *PackageManager
}

type ObjFromCartSetMemItem struct {
	CartSetOrNil *ast.FnObj
	EqualToOrNil ast.Obj
}

type PropCommutativeCase struct {
	TruePureIsCommutative  bool
	FalsePureIsCommutative bool
}

func NewCommutativePropMemItemStruct() *PropCommutativeCase {
	return &PropCommutativeCase{
		TruePureIsCommutative:  false,
		FalsePureIsCommutative: false,
	}
}

func (env *Env) GetUpMostEnv() *Env {
	if env.Parent == nil {
		return env
	}
	return env.Parent.GetUpMostEnv()
}

func (env *Env) GetSecondUpMostEnv() *Env {
	if env.Parent != nil && env.Parent.Parent == nil {
		return env
	}
	return env.Parent.GetSecondUpMostEnv()
}

func NewEnv(parent *Env) *Env {
	var packageManager *PackageManager
	if parent == nil {
		packageManager = NewPackageManager()
	} else {
		packageManager = parent.PackageManager
	}
	env := &Env{
		Parent:                 parent,
		ObjDefMem:              make(ObjDefMem),
		PropDefMem:             make(PropDefMem),
		FnTemplateDefMem:       make(FnTemplateDefMem),
		FnInFnTemplateFactsMem: make(FnInFnTMem),
		ExistPropDefMem:        make(ExistPropDefMem),
		KnownFactsStruct:       makeKnownFactsStruct(),
		EqualMem:               make(map[string]shared_ptr_to_slice_of_obj),
		// EnumFacts:              make(map[string][]ast.Obj),
		// IntensionalSetMem:        make(map[string]ast.IntensionalSetStmt),
		SymbolSimplifiedValueMem: make(map[string]ast.Obj),
		TransitivePropMem:        make(map[string]map[string][]ast.Obj),
		CommutativePropMem:       make(map[string]*PropCommutativeCase),
		AlgoDefMem:               make(map[string]*ast.DefAlgoStmt),
		DefProveAlgoMem:          make(map[string]*ast.DefProveAlgoStmt),
		PackageManager:           packageManager,
	}

	if parent == nil {
		env.ObjDefMem[glob.DoubleUnderscoreSigExist] = ast.NewDefLetStmt([]string{glob.DoubleUnderscoreSigExist}, []ast.Obj{ast.Atom(glob.DoubleUnderscoreSigExist)}, []ast.FactStmt{}, glob.BuiltinLine)
		env.ObjDefMem[glob.DoubleUnderscoreSigNotExist] = ast.NewDefLetStmt([]string{glob.DoubleUnderscoreSigNotExist}, []ast.Obj{ast.Atom(glob.DoubleUnderscoreSigNotExist)}, []ast.FactStmt{}, glob.BuiltinLine)
		env.ObjDefMem[glob.DoubleUnderscoreSigTruePure] = ast.NewDefLetStmt([]string{glob.DoubleUnderscoreSigTruePure}, []ast.Obj{ast.Atom(glob.DoubleUnderscoreSigTruePure)}, []ast.FactStmt{}, glob.BuiltinLine)
		env.ObjDefMem[glob.DoubleUnderscoreSigNotPure] = ast.NewDefLetStmt([]string{glob.DoubleUnderscoreSigNotPure}, []ast.Obj{ast.Atom(glob.DoubleUnderscoreSigNotPure)}, []ast.FactStmt{}, glob.BuiltinLine)
		env.ObjDefMem[glob.DoubleUnderscoreSigExist] = ast.NewDefLetStmt([]string{glob.DoubleUnderscoreSigExist}, []ast.Obj{ast.Atom(glob.DoubleUnderscoreSigExist)}, []ast.FactStmt{}, glob.BuiltinLine)
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

func (e *Env) NotEqualIsCommutative() {
	e.CommutativePropMem[glob.KeySymbolEqual] = NewCommutativePropMemItemStruct()
	e.CommutativePropMem[glob.KeySymbolEqual].FalsePureIsCommutative = true
}

func (e *Env) NewTransitiveProp(name string) {
	e.TransitivePropMem[name] = make(map[string][]ast.Obj)
}
