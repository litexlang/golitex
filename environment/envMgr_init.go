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
	kernel_lib "golitex/kernel_lib"
)

// template of arithmetic operations。用来证明 + $in fn(R, R)R 这样的事实
func (envMgr *EnvMgr) Init() {
	// envMgr.NewDefProp_BuiltinProp(kernel_lib.LeftIs0RightIsPositivePropDef)
	// envMgr.NewDefProp_BuiltinProp(kernel_lib.LeftIsNegativeRightIsIntegerPropDef)

	envMgr.InsertFnInFnTT(kernel_lib.AddAtom, kernel_lib.AddTemplateQ)
	envMgr.InsertFnInFnTT(kernel_lib.AddAtom, kernel_lib.AddTemplateN)
	envMgr.InsertFnInFnTT(kernel_lib.AddAtom, kernel_lib.AddTemplateZ)
	envMgr.InsertFnInFnTT(kernel_lib.AddAtom, kernel_lib.AddTemplateR)

	envMgr.InsertFnInFnTT(kernel_lib.MinusAtom, kernel_lib.MinusTemplateQ)
	envMgr.InsertFnInFnTT(kernel_lib.MinusAtom, kernel_lib.MinusTemplateN)
	envMgr.InsertFnInFnTT(kernel_lib.MinusAtom, kernel_lib.MinusTemplateZ)
	envMgr.InsertFnInFnTT(kernel_lib.MinusAtom, kernel_lib.MinusTemplateR)

	envMgr.InsertFnInFnTT(kernel_lib.StarAtom, kernel_lib.StarTemplateQ)
	envMgr.InsertFnInFnTT(kernel_lib.StarAtom, kernel_lib.StarTemplateN)
	envMgr.InsertFnInFnTT(kernel_lib.StarAtom, kernel_lib.StarTemplateZ)
	envMgr.InsertFnInFnTT(kernel_lib.StarAtom, kernel_lib.StarTemplateR)

	envMgr.InsertFnInFnTT(kernel_lib.SlashAtom, kernel_lib.SlashTemplateQ)
	envMgr.InsertFnInFnTT(kernel_lib.SlashAtom, kernel_lib.SlashTemplateN)
	envMgr.InsertFnInFnTT(kernel_lib.SlashAtom, kernel_lib.SlashTemplateZ)
	envMgr.InsertFnInFnTT(kernel_lib.SlashAtom, kernel_lib.SlashTemplateR)

	envMgr.InsertFnInFnTT(kernel_lib.ModAtom, kernel_lib.ModTemplate)

	envMgr.InsertFnInFnTT(kernel_lib.PowerAtom, kernel_lib.PowerTemplateR)

	// envMgr.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordItemExistsIn), []ast.Obj{ast.Atom(glob.KeywordSet)}, glob.BuiltinLine))

	envMgr.NewTransitiveProp(">")
	envMgr.NewTransitiveProp(">=")
	envMgr.NewTransitiveProp("<")
	envMgr.NewTransitiveProp("<=")

	envMgr.NotEqualIsCommutative()
}

func (envMgr *EnvMgr) NotEqualIsCommutative() {
	if envMgr.CurEnv().CommutativePropMem[glob.KeySymbolEqual] == nil {
		envMgr.CurEnv().CommutativePropMem[glob.KeySymbolEqual] = NewCommutativePropMemItemStruct()
	}
	envMgr.CurEnv().CommutativePropMem[glob.KeySymbolEqual].FalsePureIsCommutative = true
}

func (envMgr *EnvMgr) NewTransitiveProp(name string) {
	envMgr.CurEnv().TransitivePropMem[name] = make(map[string][]ast.Obj)
}
