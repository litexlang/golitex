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
	cmp "golitex/cmp"
)

func (env *Env) ReplaceSymbolWithValue(fc ast.Obj) (bool, ast.Obj) {
	if cmp.IsNumLitObj(fc) {
		return false, fc
	}

	switch asFc := fc.(type) {
	case ast.AtomObj:
		return env.replaceFcAtomWithValue(asFc)
	case *ast.FnObj:
		return env.replaceFcFnWithValue(asFc)
	}
	panic("")
}

func (env *Env) replaceFcFnWithValue(fc *ast.FnObj) (bool, ast.Obj) {
	if symbolValue := env.GetSymbolSimplifiedValue(fc); symbolValue != nil {
		return true, symbolValue
	}

	replaced := false
	newParams := make([]ast.Obj, len(fc.Params))
	for i, param := range fc.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewFnObj(fc.FnHead, newParams)
}

func (env *Env) replaceFcAtomWithValue(fc ast.AtomObj) (bool, ast.Obj) {
	symbolValue := env.GetSymbolSimplifiedValue(fc)
	if symbolValue == nil {
		return false, fc
	}

	return true, symbolValue
}

func (env *Env) ReplaceFcInSpecFactWithValue(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt) {
	newParams := make([]ast.Obj, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line)
}
