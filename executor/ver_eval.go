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
func (exec *Executor) evalFc(fc ast.Fc) (ast.Fc, ExecRet) {
	if cmp.IsNumLitFc(fc) {
		return fc, NewExecTrue("")
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

func (exec *Executor) evalFcFn(fc *ast.FcFn) (ast.Fc, ExecRet) {
	if symbolValue := exec.Env.GetSymbolValue(fc); symbolValue != nil {
		return symbolValue, NewExecTrue("")
	}

	if ok := exec.Env.IsFnWithDefinedAlgo(fc); ok {
		algoDef := exec.Env.GetAlgoDef(fc.FnHead.String())
		return exec.useAlgoToEvalFcFn(algoDef, fc)
	}

	return nil, NewExecUnknown("")
}

func (exec *Executor) evalFcAtom(fc ast.FcAtom) (ast.Fc, ExecRet) {
	symbolValue := exec.Env.GetSymbolValue(fc)
	if symbolValue == nil {
		return nil, NewExecUnknown("")
	}

	return symbolValue, NewExecTrue("")
}

func (exec *Executor) useAlgoToEvalFcFn(algoDef *ast.AlgoDefStmt, fcFn *ast.FcFn) (ast.Fc, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndGiveUpMsgs()

	if len(fcFn.Params) != len(algoDef.Params) {
		return nil, NewExecErr(fmt.Sprintf("algorithm %s requires %d parameters, get %d instead", algoDef.FuncName, len(algoDef.Params), len(fcFn.Params)))
	}

	// 传入的参数真的在fn的domain里
	execRet := exec.fcfnParamsInFnDomain(fcFn)
	if !execRet.IsTrue() {
		return nil, NewExecErr(fmt.Sprintf("parameters of %s are not in domain of %s", fcFn, fcFn.FnHead))
	}

	for _, param := range algoDef.Params {
		if exec.Env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			panic("TODO: 之后如果外面已经弄过了，那就遍历地变成无重复的随机符号")
		}
	}

	fcFnParamsValues := []ast.Fc{}
	for _, param := range fcFn.Params {
		_, value := exec.Env.ReplaceSymbolWithValue(param)
		if cmp.IsNumLitFc(value) {
			fcFnParamsValues = append(fcFnParamsValues, value)
		} else {
			return nil, NewExecErr(fmt.Sprintf("value of %s of %s is unknown.", param, fcFn))
		}
	}

	fcFnWithValueParams := ast.NewFcFn(fcFn.FnHead, fcFnParamsValues)

	uniMap := map[string]ast.Fc{}
	for i, param := range algoDef.Params {
		uniMap[param] = fcFnParamsValues[i]
	}

	instAlgoDef, err := algoDef.Instantiate(uniMap)
	if err != nil {
		return nil, NewExecErrWithErr(err)
	}

	value, execRet := exec.runAlgoStmts(instAlgoDef.(*ast.AlgoDefStmt).Stmts, fcFnWithValueParams)
	return value, execRet
}

func (exec *Executor) runAlgoStmts(algoStmts ast.AlgoSlice, fcFnWithValueParams *ast.FcFn) (ast.Fc, ExecRet) {
	for _, stmt := range algoStmts {
		switch asStmt := stmt.(type) {
		case *ast.AlgoReturnStmt:
			execRet, err := exec.factStmt(ast.EqualFact(fcFnWithValueParams, asStmt.Value))
			if err != nil || !execRet.IsTrue() {
				return nil, execRet
			}
			return exec.evalFc(asStmt.Value)
		case *ast.AlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); !execRet.IsTrue() {
				return nil, execRet
			} else if conditionIsTrue {
				return exec.evalAlgoIf(asStmt, fcFnWithValueParams)
			}
		default:
			execRet, _, err := exec.Stmt(stmt.(ast.Stmt))
			if err != nil || !execRet.IsTrue() {
				return nil, execRet
			}
		}
	}

	return nil, NewExecErr(fmt.Sprintf("There is no return value."))
}

func (exec *Executor) fcfnParamsInFnDomain(fcFn *ast.FcFn) ExecRet {
	ver := NewVerifier(exec.Env)
	return ver.fcSatisfyFnRequirement(fcFn, Round0NoMsg)
}

func (exec *Executor) IsAlgoIfConditionTrue(stmt *ast.AlgoIfStmt) (bool, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndGiveUpMsgs()

	for _, fact := range stmt.Conditions {
		execRet, err := exec.factStmt(fact)
		if err != nil || execRet.IsErr() {
			return false, NewExecErrWithErr(err)
		}

		if execRet.IsTrue() {
			continue
		}

		factAsReversibleFact, reversed := fact.(ast.Spec_OrFact)
		if !reversed {
			return false, NewExecErr(fmt.Sprintf("The condition %s in\n%s\nis unknown, and it can not be negated. Failed", fact, stmt))
		}

		for _, reversedFact := range factAsReversibleFact.ReverseIsTrue() {
			execRet, err := exec.factStmt(reversedFact)
			if err != nil || execRet.IsErr() {
				return false, NewExecErrWithErr(err)
			}

			if !execRet.IsTrue() {
				return false, NewExecErr(fmt.Sprintf("%s is unknown. Negation of it is also unknown. Fail to verify condition of if statement:\n%s", fact, stmt))
			}
		}

		return false, NewExecTrue("")
	}

	return true, NewExecTrue("")
}

func (exec *Executor) evalAlgoIf(stmt *ast.AlgoIfStmt, fcFnWithValueParams *ast.FcFn) (ast.Fc, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndGiveUpMsgs()

	// all conditions are true
	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	err := exec.knowStmt(knowStmt)
	if err != nil {
		return nil, NewExecErrWithErr(err)
	}

	value, execRet := exec.runAlgoStmts(stmt.ThenStmts, fcFnWithValueParams)
	return value, execRet
}
