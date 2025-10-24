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
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (env *Env) ReplaceSymbolWithValueAndCompute(fc ast.Fc) (bool, ast.Fc, error) {
	if cmp.IsNumLitFc(fc) {
		return false, fc, nil
	}

	switch asFc := fc.(type) {
	case ast.FcAtom:
		return env.replaceFcAtomWithValueAndCompute(asFc)
	case *ast.FcFn:
		return env.replaceFcFnWithValueAndCompute(asFc)
	}
	panic("")
}

func (env *Env) replaceFcFnWithValueAndCompute(fc *ast.FcFn) (bool, ast.Fc, error) {
	if ok := env.IsFnWithDefinedAlgo(fc); ok {
		computed, ok, err := env.Compute(fc) // 哪怕没算出来，也是可能的
		if err != nil {
			return false, nil, fmt.Errorf("error computing: %s", fc)
		}
		if ok {
			return true, computed, nil
		}
	}

	if symbolValue, ok := env.GetSymbolValue(fc); ok {
		return true, symbolValue, nil
	}

	replaced := false
	newParams := make([]ast.Fc, len(fc.Params))
	for i, param := range fc.Params {
		var newReplaced bool
		var err error
		newReplaced, newParams[i], err = env.ReplaceSymbolWithValueAndCompute(param)
		if err != nil {
			return false, nil, fmt.Errorf("error replacing symbol with value: %s", param)
		}

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewFcFn(fc.FnHead, newParams), nil
}

func (env *Env) replaceFcAtomWithValueAndCompute(fc ast.FcAtom) (bool, ast.Fc, error) {
	symbolValue, ok := env.GetSymbolValue(fc)
	if !ok {
		return false, fc, nil
	}

	return true, symbolValue, nil
}

// TODO: 未来有一天，会被用来替换 SpecFactStmt 中的 Fc 为 计算后的 Fc
func (env *Env) ReplaceFcInSpecFactWithValueAndCompute(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt, error) {
	newParams := make([]ast.Fc, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		var err error
		newReplaced, newParams[i], err = env.ReplaceSymbolWithValueAndCompute(param)
		if err != nil {
			return false, nil, fmt.Errorf("error replacing symbol with value: %s", param)
		}

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line), nil
}
