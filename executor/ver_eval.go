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
	glob "golitex/glob"
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
		algoDef := exec.Env.GetAlgoDef(fc.FnHead.String())
		return exec.useAlgoToEvalFcFn(algoDef, fc)
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

	// 传入的参数真的在fn的domain里
	execRet := exec.fcfnParamsInFnDomain(fcFn)
	if !execRet.IsTrue() {
		return nil, fmt.Errorf("parameters of %s are not in domain of %s", fcFn, fcFn.FnHead)
	}

	// 为了防止proof中又声明了同名的对象，我们保证环境里已经申明了algoDef的param：1. 如果同名的东西已经在大环境里了，那OK 2. 如果不在，那就申明一下
	for _, param := range algoDef.Params {
		if !exec.Env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			exec.defLetStmt(ast.NewDefObjStmt([]string{param}, []ast.Fc{ast.FcAtom(glob.KeywordObj)}, []ast.FactStmt{}, algoDef.GetLine()))
		}
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

func (exec *Executor) fcfnParamsInFnDomain(fcFn *ast.FcFn) ExecRet {
	ver := NewVerifier(exec.Env)
	return ver.fcSatisfyFnRequirement(fcFn, Round0NoMsg)
}
