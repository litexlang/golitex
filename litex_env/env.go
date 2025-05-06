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
	ast "golitex/litex_ast"
)

type Env struct {
	Parent *Env
	Msgs   []string

	ObjMem       ObjMem
	PropMem      PropMem
	FnMem        FnMem
	ExistPropMem ExistPropMem
	SetMem       SetMem

	SpecFactMem            SpecFactMem
	SpecFactInLogicExprMem SpecFactInLogicExprMem
	SpecFactInUniFactMem   SpecFactInUniFactMem

	EmitWhenSpecFactIsTrueMem EmitWhenSpecFactIsTrueMem
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

		SpecFactMem:            *newSpecFactMem(),
		SpecFactInLogicExprMem: *NewSpecFactInLogicExprMem(),
		SpecFactInUniFactMem:   *NewSpecFactInUniFact(),

		EmitWhenSpecFactIsTrueMem: *NewEmitWhenSpecFactIsTrueMem(),
	}

	return env
}

func (e *Env) NewMsg(s string) {
	e.Msgs = append(e.Msgs, s)
}

func (e *Env) GetExistPropDef(propName ast.FcAtom) (*ast.DefConExistPropStmt, bool) {
	// recursively search parent envs
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropMem.Get(propName)
		if ok {
			return existProp, true
		}
	}
	return nil, false
}

func (e *Env) GetPropDef(propName ast.FcAtom) (*ast.DefConPropStmt, bool) {
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
