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

type shared_ptr_to_slice_of_fc = *[]ast.Fc

type KnownFactsStruct struct {
	SpecFactMem                       SpecFactMem
	SpecFactInLogicExprMem            SpecFactInLogicExprMem
	SpecFactInUniFactMem              SpecFactInUniFactMem
	SpecFact_InLogicExpr_InUniFactMem SpecFact_InLogicExpr_InUniFactMem
}

type Env struct {
	Parent *Env
	Msgs   []string

	ObjDefMem       ObjDefMem
	PropDefMem      PropDefMem
	FnDefMem        FnDefMem // 即使我会存 f in f(paramset)retSet,这个项仍然必要，因为我在验证prop里的参数符合prop的要求时要用定义。而且即使后者也不必要，我放着总没错
	ExistPropDefMem ExistPropDefMem
	// SetDefMem       SetDefMem

	KnownFactsStruct KnownFactsStruct

	// 考虑多个系统的时候，再引入 map[string]string
	EqualMem map[string]shared_ptr_to_slice_of_fc

	KnownFactInMatchEnv glob.Map2D[KnownFactsStruct]

	CurMatchEnv *ast.SupposePropMatchStmt
}

func NewEnv(parent *Env, curMatchEnv *ast.SupposePropMatchStmt) *Env {
	env := &Env{
		Parent: parent,
		Msgs:   []string{},

		ObjDefMem:       *newObjMemory(),
		PropDefMem:      *newPropMemory(),
		FnDefMem:        *newFnMemory(),
		ExistPropDefMem: *newExistPropMemory(),
		// SetDefMem:       *newSetMemory(),

		KnownFactsStruct: makeKnownFactsStruct(),

		EqualMem: make(map[string]shared_ptr_to_slice_of_fc),

		KnownFactInMatchEnv: make(glob.Map2D[KnownFactsStruct]),

		CurMatchEnv: curMatchEnv,
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

// func (e *Env) IsSpecFactPropCommutative(fact *ast.SpecFactStmt) bool {
// 	// 如果是等号那自动成立
// 	if ast.IsFcAtomWithName(&fact.PropName, glob.KeySymbolEqual) {
// 		return true
// 	}

// for env := e; env != nil; env = env.Parent {
// 	if env.IsCommutativeProp(fact.PropName) {
// 		return true
// 	}
// }
// 	return false
// }
