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

func (exec *Executor) byStmt(stmt *ast.ByStmt) ExecRet {
	if len(stmt.ThenFacts) > 0 {
		exec.NewEnv(exec.Env)
		defer exec.deleteEnvAndGiveUpMsgs()
	}

	execState := exec.callProveAlgo(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	if len(stmt.ThenFacts) > 0 {
		for _, fact := range stmt.ThenFacts {
			execState, err := exec.factStmt(fact)
			if err != nil {
				return NewExecErr("")
			}
			if execState.IsNotTrue() {
				return execState
			}
		}
	}

	return NewExecTrue("")
}

func (exec *Executor) callProveAlgo(stmt *ast.ByStmt) ExecRet {
	// params of stmt must be numeric literals
	numExprFcs := []ast.Fc{}
	for _, param := range stmt.Params {
		value, execRet := exec.verifyIsNumExprFcOrHasValueThenSimplify(param)
		if execRet.IsNotTrue() {
			return execRet
		}
		numExprFcs = append(numExprFcs, value)
	}

	proveAlgoDef := exec.Env.GetAlgoDef(stmt.ProveAlgoName)
	if proveAlgoDef == nil {
		return NewExecErr(fmt.Sprintf("prove algo %s not found", stmt.ProveAlgoName))
	}

	if len(proveAlgoDef.Params) != len(stmt.Params) {
		return NewExecErr(fmt.Sprintf("prove algo %s requires %d params, get %d instead", stmt.ProveAlgoName, len(proveAlgoDef.Params), len(stmt.Params)))
	}

	for _, param := range proveAlgoDef.Params {
		if exec.Env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			panic("TODO: 之后如果外面已经弄过了，那就遍历地变成无重复的随机符号。之所以这里要panic是因为，可能用户在algo def 里面声明了和外面同名的符号")
		}
	}

	paramsValues := []ast.Fc{}
	for _, param := range stmt.Params {
		_, value := exec.Env.ReplaceSymbolWithValue(param)
		// simplifiedValue := value
		simplifiedValue, execRet := exec.simplifyNumExprFc(value)
		if execRet.IsNotTrue() {
			return NewExecErr(fmt.Sprintf("value of %s of %s is unknown.", param, stmt.ProveAlgoName))
		}
		paramsValues = append(paramsValues, simplifiedValue)
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range proveAlgoDef.Params {
		uniMap[param] = paramsValues[i]
	}

	instProveAlgoDef, err := proveAlgoDef.Instantiate(uniMap)
	if err != nil {
		return NewExecErrWithErr(err)
	}

	execRet := exec.runAlgoStmtsWhenProveByProveAlgo(instProveAlgoDef.(*ast.DefProveAlgoStmt), paramsValues)
	if execRet.IsNotTrue() {
		return execRet
	}

	return NewExecTrue("")
}

func (exec *Executor) verifyIsNumExprFcOrHasValueThenSimplify(fc ast.Fc) (ast.Fc, ExecRet) {
	if cmp.IsNumLitFc(fc) {
		return exec.simplifyNumExprFc(fc)
	}

	value := exec.Env.GetSymbolSimplifiedValue(fc)
	if value == nil {
		return nil, NewExecErr(fmt.Sprintf("symbol %s has no value", fc.String()))
	}

	return value, NewExecTrue("")
}

func (exec *Executor) runAlgoStmtsWhenProveByProveAlgo(instProveAlgoDef *ast.DefProveAlgoStmt, paramsValues []ast.Fc) ExecRet {
	panic("")
}
