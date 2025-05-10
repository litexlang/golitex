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

type Env struct {
	Parent *Env
	Msgs   []string

	ObjMem       ObjMem
	PropMem      PropMem
	FnMem        FnMem
	ExistPropMem ExistPropMem
	SetMem       SetMem

	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
	EmitWhenSpecFactIsTrueMem         EmitWhenSpecFactIsTrueMem

	CommutativeProp map[string]map[string]struct{}

	// 为了让我日子好过，我不允许用户用以 fcFn 形式为fn header的 fn 名来定义 commutative fn
	CommutativeFn map[string]map[string]struct{}
	AssociativeFn map[string]map[string]struct{}

	// 考虑多个系统的时候，再引入 map[string]string
	EqualMem    map[string]*[]ast.Fc
	EqualFnMem  map[string]*[]ast.Fc
	EqualSetMem map[string]*[]ast.Fc
}

func NewEnv(parent *Env) *Env {
	env := &Env{
		Parent: parent,
		Msgs:   []string{},

		ObjMem:       *NewObjMemory(),
		PropMem:      *NewPropMemory(),
		FnMem:        *NewFnMemory(),
		ExistPropMem: *NewExistPropMemory(),
		SetMem:       *NewSetMemory(),

		SpecFactMem:                       *newSpecFactMem(),
		SpecFactInLogicExprMem:            *NewSpecFactInLogicExprMem(),
		SpecFactInUniFactMem:              *NewSpecFactInUniFact(),
		SpecFact_InLogicExpr_InUniFactMem: *NewSpecFact_InLogicExpr_InUniFactMem(),

		EmitWhenSpecFactIsTrueMem: *NewEmitWhenSpecFactIsTrueMem(),

		CommutativeProp: make(map[string]map[string]struct{}),
		CommutativeFn:   make(map[string]map[string]struct{}),
		AssociativeFn:   make(map[string]map[string]struct{}),

		EqualMem: make(map[string]*[]ast.Fc),
	}
	return env
}

func (e *Env) InsertCommutativeProp(propName ast.FcAtom) {
	if _, ok := e.CommutativeProp[propName.PkgName]; !ok {
		e.CommutativeProp[propName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.CommutativeProp[propName.PkgName][propName.Name]; !ok {
		e.CommutativeProp[propName.PkgName][propName.Name] = struct{}{}
	}
}

func (e *Env) IsCommutativeProp(propName ast.FcAtom) bool {
	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&propName, glob.KeySymbolEqual) {
		return true
	}

	if _, ok := e.CommutativeProp[propName.PkgName][propName.Name]; ok {
		return true
	}
	return false
}

func (e *Env) InsertCommutativeFn(fnName ast.FcAtom) {
	if _, ok := e.CommutativeFn[fnName.PkgName]; !ok {
		e.CommutativeFn[fnName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.CommutativeFn[fnName.PkgName][fnName.Name]; !ok {
		e.CommutativeFn[fnName.PkgName][fnName.Name] = struct{}{}
	}
}

func (e *Env) IsCommutativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fnName, glob.KeySymbolStar) {
		return true
	}

	if _, ok := e.CommutativeFn[fnName.PkgName][fnName.Name]; ok {
		return true
	}
	return false
}

func (e *Env) InsertAssociativeFn(fnName ast.FcAtom) {
	if _, ok := e.AssociativeFn[fnName.PkgName]; !ok {
		e.AssociativeFn[fnName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.AssociativeFn[fnName.PkgName][fnName.Name]; !ok {
		e.AssociativeFn[fnName.PkgName][fnName.Name] = struct{}{}
	}
}

func (e *Env) IsAssociativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fnName, glob.KeySymbolStar) {
		return true
	}

	if _, ok := e.AssociativeFn[fnName.PkgName][fnName.Name]; ok {
		return true
	}
	return false
}

func (e *Env) NewMsg(s string) {
	e.Msgs = append(e.Msgs, s)
}

func (e *Env) GetExistPropDef(propName ast.FcAtom) (*ast.DefExistPropStmt, bool) {
	// recursively search parent envs
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropMem.Get(propName)
		if ok {
			return existProp, true
		}
	}
	return nil, false
}

func (e *Env) GetPropDef(propName ast.FcAtom) (*ast.DefPropStmt, bool) {
	// recursively search parent envs
	for env := e; env != nil; env = env.Parent {
		prop, ok := env.PropMem.Get(propName)
		if ok {
			return prop, true
		}
	}
	return nil, false
}

func (e *Env) GetFcAtomDef(fcAtomName *ast.FcAtom) (ast.DefStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		fcAtomDef, ok := env.getFcAtomDefAtCurEnv(fcAtomName)
		if ok {
			return fcAtomDef, true
		}
	}
	return nil, false
}

func (e *Env) getFcAtomDefAtCurEnv(fcAtomName *ast.FcAtom) (ast.DefStmt, bool) {
	// Case1: It is a prop
	prop, ok := e.PropMem.Get(*fcAtomName)
	if ok {
		return prop, true
	}

	// Case2: It is a fn
	fn, ok := e.FnMem.Get(*fcAtomName)
	if ok {
		return fn, true
	}

	// Case3: It is a exist prop
	existProp, ok := e.ExistPropMem.Get(*fcAtomName)
	if ok {
		return existProp, true
	}

	// Case4: It is a obj
	obj, ok := e.ObjMem.Get(*fcAtomName)
	if ok {
		return obj, true
	}

	return nil, false
}

func NewEmitWhenSpecFactIsTrueMem() *EmitWhenSpecFactIsTrueMem {
	return &EmitWhenSpecFactIsTrueMem{
		Dict: make(map[string]map[string][]ast.UniFactStmt),
	}
}

func (e *Env) IsSpecFactPropCommutative(fact *ast.SpecFactStmt) bool {
	// 如果是等号那自动成立
	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeySymbolEqual) {
		return true
	}

	for env := e; env != nil; env = env.Parent {
		if env.IsCommutativeProp(fact.PropName) {
			return true
		}
	}
	return false
}

func (e *Env) GetSetDef(set ast.Fc) (*ast.SetDefSetBuilderStmt, bool) {
	setAsAtom, isSetAsAtom := set.(*ast.FcAtom)
	if !isSetAsAtom {
		return nil, false
	}

	for env := e; env != nil; env = env.Parent {
		setDef, ok := env.SetMem.Get(setAsAtom.PkgName, setAsAtom.Name)
		if ok {
			return setDef, true
		}
	}
	return nil, false
}

func (e *Env) GetFnDef(fn ast.Fc) (*ast.DefFnStmt, bool) {
	fnAsAtom, isFnAsAtom := fn.(*ast.FcAtom)
	if !isFnAsAtom {
		return nil, false
	}

	for env := e; env != nil; env = env.Parent {
		fnDef, ok := env.FnMem.Get(*fnAsAtom)
		if ok {
			return fnDef, true
		}
	}
	return nil, false
}
