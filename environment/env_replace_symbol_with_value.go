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

func (env *Env) ReplaceSymbolWithValue(fc ast.Fc) (bool, ast.Fc) {
	if toCompute, ok := ast.IsFcFnWithCompHeadAndReturnFcToCompute(fc); ok {
		computed, ok, err := env.Compute(toCompute)
		if err != nil || !ok {
			panic(err)
		}
		return true, computed
	}

	if cmp.IsNumLitFc(fc) {
		return false, fc
	}

	switch asFc := fc.(type) {
	case ast.FcAtom:
		return env.replaceFcAtomWithValue(asFc)
	case *ast.FcFn:
		return env.replaceFcFnWithValue(asFc)
	}
	panic("")
}

func (env *Env) replaceFcFnWithValue(fc *ast.FcFn) (bool, ast.Fc) {
	if symbolValue, ok := env.GetSymbolValue(fc); ok {
		return true, symbolValue
	}

	replaced := false
	newParams := make([]ast.Fc, len(fc.Params))
	for i, param := range fc.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)
		replaced = replaced || newReplaced
	}
	return replaced, ast.NewFcFn(fc.FnHead, newParams)
}

func (env *Env) replaceFcAtomWithValue(fc ast.FcAtom) (bool, ast.Fc) {
	symbolValue, ok := env.GetSymbolValue(fc)
	if !ok {
		return false, fc
	}

	return true, symbolValue
}

func (env *Env) ReplaceFcInSpecFact(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt) {
	newParams := make([]ast.Fc, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		newReplaced, newParams[i] = env.ReplaceSymbolWithValue(param)
		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line)
}
