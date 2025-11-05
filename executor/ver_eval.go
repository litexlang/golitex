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

// 这里 bool 表示，是否启动过 用algo 计算；如果仅仅是用 algo 来计算，那是不会返回true的
func (exec *Executor) evalFc(fc ast.Fc) (ast.Fc, error) {
	if cmp.IsNumLitFc(fc) {
		return fc, nil
	}

	switch asFc := fc.(type) {
	case ast.FcAtom:
		return exec.evalFcAtom(asFc)
	case *ast.FcFn:
		return exec.evalFcFn(asFc)
	default:
		panic(fmt.Sprintf("unexpected type: %T", fc))
	}
}

func (exec *Executor) evalFcFn(fc *ast.FcFn) (ast.Fc, error) {
	if symbolValue := exec.Env.GetSymbolValue(fc); symbolValue != nil {
		return symbolValue, nil
	}

	if ok := exec.Env.IsFnWithDefinedAlgo(fc); ok {
		newParams := make([]ast.Fc, len(fc.Params))
		for i, param := range fc.Params {
			var err error

			newParams[i], err = exec.evalFc(param)
			if err != nil {
				return nil, err
			} else if newParams[i] == nil {
				return nil, nil
			}
		}

		return ast.NewFcFn(fc.FnHead, newParams), nil
	}

	return nil, nil
}

func (exec *Executor) evalFcAtom(fc ast.FcAtom) (ast.Fc, error) {
	symbolValue := exec.Env.GetSymbolValue(fc)
	if symbolValue == nil {
		return nil, nil
	}

	return symbolValue, nil
}

func (exec *Executor) useAlgoToEvalFcFn(algoDef *ast.AlgoDefStmt, fcFn *ast.FcFn) (ast.Fc, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndGiveUpMsgs()

	if len(fcFn.Params) != len(algoDef.Params) {
		return nil, fmt.Errorf("algorithm %s requires %d parameters, get %d instead", algoDef.FuncName, len(algoDef.Params), len(fcFn.Params))
	}

	fcFnParamsValue := []ast.Fc{}
	for _, param := range fcFn.Params {
		_, value := exec.Env.ReplaceSymbolWithValue(param)
		fcFnParamsValue = append(fcFnParamsValue, value)
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range algoDef.Params {
		uniMap[param] = fcFnParamsValue[i]
	}

	instAlgoDef, err := algoDef.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	for _, stmt := range instAlgoDef.(*ast.AlgoDefStmt).Stmts {
		switch asStmt := stmt.(type) {
		case *ast.AlgoReturnStmt:
			return exec.evalFc(asStmt.Value)
		default:
			panic("")
		}
	}

	return nil, fmt.Errorf(fmt.Sprintf("There is no return value of %s", fcFn.String()))
}
