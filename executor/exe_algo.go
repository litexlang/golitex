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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (exec *Executor) algoDefStmt(stmt *ast.AlgoDefStmt) (ExecRet, error) {
	if _, ok := exec.env.AlgoDefMem[stmt.FuncName]; !ok {
		exec.env.AlgoDefMem[stmt.FuncName] = []*ast.AlgoDefStmt{}
	}
	exec.env.AlgoDefMem[stmt.FuncName] = append(exec.env.AlgoDefMem[stmt.FuncName], stmt)
	exec.newMsg(stmt.String())
	return NewExecTrue(""), nil
}

// 这里 bool 表示，是否启动过 用algo 计算；如果仅仅是用 algo 来计算，那是不会返回true的
func (exec *Executor) ReplaceSymbolWithValueAndCompute(fc ast.Fc) (bool, ast.Fc, error) {
	if cmp.IsNumLitFc(fc) {
		return false, fc, nil
	}

	switch asFc := fc.(type) {
	case ast.FcAtom:
		return exec.replaceFcAtomWithValueAndCompute(asFc)
	case *ast.FcFn:
		return exec.replaceFcFnWithValueAndCompute(asFc)
	default:
		panic(fmt.Sprintf("unexpected type: %T", fc))
	}
}

func (exec *Executor) replaceFcFnWithValueAndCompute(fc *ast.FcFn) (bool, ast.Fc, error) {
	if symbolValue := exec.env.GetSymbolValue(fc); symbolValue != nil {
		return false, symbolValue, nil
	}

	newParams := make([]ast.Fc, len(fc.Params))
	replaced := false
	for i, param := range fc.Params {
		var err error
		newReplaced := false
		newReplaced, newParams[i], err = exec.ReplaceSymbolWithValueAndCompute(param)
		if err != nil {
			return false, nil, fmt.Errorf("error replacing symbol with value: %s", param)
		}
		replaced = replaced || newReplaced
	}

	ret := ast.NewFcFn(fc.FnHead, newParams)

	if ok := exec.env.IsFnWithDefinedAlgo(fc); ok {
		for i := range len(newParams) {
			if !cmp.IsNumLitFc(newParams[i]) {
				return replaced, ret, nil
			}
		}

		computed, err := exec.env.Compute(ret) // 哪怕没算出来，也是可能的
		if err != nil {
			return false, nil, fmt.Errorf("error computing: %s", fc)
		}
		if computed != nil {
			return true, computed, nil
		}
	}

	return replaced, ret, nil
}

func (exec *Executor) replaceFcAtomWithValueAndCompute(fc ast.FcAtom) (bool, ast.Fc, error) {
	symbolValue := exec.env.GetSymbolValue(fc)
	if symbolValue == nil {
		return false, fc, nil
	}

	return false, symbolValue, nil
}

// TODO: 未来有一天，会被用来替换 SpecFactStmt 中的 Fc 为 计算后的 Fc
func (exec *Executor) ReplaceFcInSpecFactWithValueAndCompute(fact *ast.SpecFactStmt) (bool, *ast.SpecFactStmt, error) {
	newParams := make([]ast.Fc, len(fact.Params))
	replaced := false
	for i, param := range fact.Params {
		var newReplaced bool
		var err error
		newReplaced, newParams[i], err = exec.ReplaceSymbolWithValueAndCompute(param)
		if err != nil {
			return false, nil, fmt.Errorf("error replacing symbol with value: %s", param)
		}

		replaced = replaced || newReplaced
	}
	return replaced, ast.NewSpecFactStmt(fact.TypeEnum, fact.PropName, newParams, fact.Line), nil
}
