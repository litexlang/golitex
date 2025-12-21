// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

// import (
// 	ast "golitex/ast"
// )

// // 因为 in 类型的事实很多，考虑把objString为key保留一个map，记录它在什么集合里。比如 a $in N 就保存成 key:a values:[]{N}
// type Env struct {
// 	Parent *Env

// 	ObjDefMem        AtomObjDefMem
// 	PropDefMem       PropDefMem
// 	FnTemplateDefMem FnTemplateDefMem
// 	ExistPropDefMem  ExistPropDefMem

// 	KnownFactsStruct KnownFactsStruct

// 	FnInFnTemplateFactsMem FnInFnTMem

// 	EqualMem                 map[string]shared_ptr_to_slice_of_obj
// 	SymbolSimplifiedValueMem map[string]ast.Obj

// 	TransitivePropMem  map[string]map[string][]ast.Obj
// 	CommutativePropMem map[string]*PropCommutativeCase

// 	AlgoDefMem map[string]*ast.DefAlgoStmt

// 	DefProveAlgoMem map[string]*ast.DefProveAlgoStmt

// 	PackageManager *EnvPkgMgr
// }

// func (env *Env) GetUpMostEnv() *Env {
// 	if env.Parent == nil {
// 		return env
// 	}
// 	return env.Parent.GetUpMostEnv()
// }

// func (env *Env) GetSecondUpMostEnv() *Env {
// 	if env.Parent != nil && env.Parent.Parent == nil {
// 		return env
// 	}
// 	return env.Parent.GetSecondUpMostEnv()
// }

// func NewEnv(parent *Env) *Env {
// 	var packageManager *EnvPkgMgr
// 	if parent == nil {
// 		packageManager = NewPackageManager()
// 	} else {
// 		packageManager = parent.PackageManager
// 	}
// 	env := &Env{
// 		Parent:                   parent,
// 		ObjDefMem:                make(AtomObjDefMem),
// 		PropDefMem:               make(PropDefMem),
// 		FnTemplateDefMem:         make(FnTemplateDefMem),
// 		FnInFnTemplateFactsMem:   make(FnInFnTMem),
// 		ExistPropDefMem:          make(ExistPropDefMem),
// 		KnownFactsStruct:         makeKnownFactsStruct(),
// 		EqualMem:                 make(map[string]shared_ptr_to_slice_of_obj),
// 		SymbolSimplifiedValueMem: make(map[string]ast.Obj),
// 		TransitivePropMem:        make(map[string]map[string][]ast.Obj),
// 		CommutativePropMem:       make(map[string]*PropCommutativeCase),
// 		AlgoDefMem:               make(map[string]*ast.DefAlgoStmt),
// 		DefProveAlgoMem:          make(map[string]*ast.DefProveAlgoStmt),
// 		PackageManager:           packageManager,
// 	}
// 	return env
// }
