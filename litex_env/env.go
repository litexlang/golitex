// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import (
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
)

type Env struct {
	Parent *Env
	Msgs   []string

	ObjMem       mem.ObjMem
	PropMem      mem.PropMem
	FnMem        mem.FnMem
	ExistPropMem mem.ExistPropMem

	SpecFactMem  mem.SpecFactMemDict
	CondFactMem  mem.CondFactMemDict
	UniFactMem   mem.UniFactMemDict
	EqualFactMem mem.EqualFactMem

	//TODO 这里必须区分Concrete和Generic. 默认不加前缀的是普通的事实；有Generic前缀的是Generic

	UniParamMap map[string]ast.Fc

	CurPkg string
}

func NewEnv(parent *Env, uniParamMap map[string]ast.Fc, curPkg string) *Env {
	if uniParamMap == nil {
		uniParamMap = make(map[string]ast.Fc)
	}

	env := &Env{
		Parent: parent,
		Msgs:   []string{},

		ObjMem:       *mem.NewObjMemory(),
		PropMem:      *mem.NewPropMemory(),
		FnMem:        *mem.NewFnMemory(),
		ExistPropMem: *mem.NewExistPropMemory(),

		SpecFactMem:  *mem.NewSpecFactMemDict(),
		CondFactMem:  *mem.NewCondFactMemDict(),
		UniFactMem:   *mem.NewUniFactMemDict(),
		EqualFactMem: *newEqualFactMem(),

		UniParamMap: uniParamMap,

		CurPkg: curPkg,
	}

	return env
}

func newEqualFactMem() *mem.EqualFactMem {
	return &mem.EqualFactMem{Mem: *glob.NewRedBlackTree(cmp.EqualFactMemoryTreeNodeCompare)}
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
