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

func (exec *Executor) simplifyNumExprFc(fc ast.Fc) (ast.Fc, ExecRet) {
	simplifiedNumExprFc := cmp.IsNumExprFcThenSimplify(fc)
	if simplifiedNumExprFc == nil {
		return nil, NewExecErr("")
	}

	return simplifiedNumExprFc, NewExecTrue("")
}

// 这里 bool 表示，是否启动过 用algo 计算；如果仅仅是用 algo 来计算，那是不会返回true的
func (exec *Executor) evalFcThenSimplify(fc ast.Fc) (ast.Fc, ExecRet) {
	// fmt.Println(fc)

	if cmp.IsNumLitFc(fc) {
		return exec.simplifyNumExprFc(fc)
	}

	switch asFc := fc.(type) {
	case ast.FcAtom:
		symbolValue := exec.Env.GetSymbolSimplifiedValue(fc)
		if symbolValue == nil {
			return nil, NewExecErr(fmt.Sprintf("symbol %s has no value", fc.String()))
		}
		return symbolValue, NewExecTrue("")
	case *ast.FcFn:
		return exec.evalFcFnThenSimplify(asFc)
	default:
		return nil, NewExecErr(fmt.Sprintf("unexpected type: %T", fc))
	}
}

var basicArithOptMap = map[string]struct{}{
	glob.KeySymbolPlus:    {},
	glob.KeySymbolMinus:   {},
	glob.KeySymbolStar:    {},
	glob.KeySymbolSlash:   {},
	glob.KeySymbolPower:   {},
	glob.KeySymbolPercent: {},
}

// 可能返回数值的时候需要检查一下会不会除以0这种情况
func (exec *Executor) evalFcFnThenSimplify(fc *ast.FcFn) (ast.Fc, ExecRet) {
	if symbolValue := exec.Env.GetSymbolSimplifiedValue(fc); symbolValue != nil {
		return symbolValue, NewExecTrue("")
	}

	if ast.IsFcFnWithHeadNameInSlice(fc, basicArithOptMap) {
		left, execRet := exec.evalFcThenSimplify(fc.Params[0])
		if execRet.IsNotTrue() {
			return nil, execRet
		}
		right, execRet := exec.evalFcThenSimplify(fc.Params[1])
		if execRet.IsNotTrue() {
			return nil, execRet
		}

		numExprFc := ast.NewFcFn(fc.FnHead, []ast.Fc{left, right})
		execRet = exec.fcfnParamsInFnDomain(numExprFc)
		if execRet.IsNotTrue() {
			return nil, NewExecErr(fmt.Sprintf("%s = %s is invalid", fc, numExprFc))
		}

		return exec.simplifyNumExprFc(numExprFc)
	}

	if ok := exec.Env.IsFnWithDefinedAlgo(fc); ok {
		numExprFc, execRet := exec.useAlgoToEvalFcFnThenSimplify(fc)
		if execRet.IsNotTrue() {
			return nil, execRet
		}

		return numExprFc, NewExecTrue("")
	}

	return nil, NewExecUnknown("")
}

func (exec *Executor) useAlgoToEvalFcFnThenSimplify(fcFn *ast.FcFn) (ast.Fc, ExecRet) {
	algoDef := exec.Env.GetAlgoDef(fcFn.FnHead.String())
	if algoDef == nil {
		return nil, NewExecErr(fmt.Sprintf("algo %s is not found", fcFn.FnHead.String()))
	}

	if len(fcFn.Params) != len(algoDef.Params) {
		return nil, NewExecErr(fmt.Sprintf("algorithm %s requires %d parameters, get %d instead", algoDef.FuncName, len(algoDef.Params), len(fcFn.Params)))
	}

	// 传入的参数真的在fn的domain里
	execRet := exec.fcfnParamsInFnDomain(fcFn)
	if execRet.IsNotTrue() {
		return nil, NewExecErr(fmt.Sprintf("parameters of %s are not in domain of %s", fcFn, fcFn.FnHead))
	}

	for i, param := range algoDef.Params {
		if exec.Env.IsAtomDeclared(ast.FcAtom(param), map[string]struct{}{}) {
			continue
		} else {
			err := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Fc{ast.FcAtom(glob.KeywordObj)}, []ast.FactStmt{ast.NewEqualFact(ast.FcAtom(param), fcFn.Params[i])}, glob.InnerGenLine))
			if err != nil {
				return nil, NewExecErr(err.Error())
			}
		}
	}

	fcFnParamsValues := []ast.Fc{}
	for _, param := range fcFn.Params {
		_, value := exec.Env.ReplaceSymbolWithValue(param)
		// simplifiedValue := value
		simplifiedValue, execRet := exec.simplifyNumExprFc(value)
		if execRet.IsNotTrue() {
			return nil, NewExecErr(fmt.Sprintf("value of %s of %s is unknown.", param, fcFn))
		}
		fcFnParamsValues = append(fcFnParamsValues, simplifiedValue)
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

	value, execRet := exec.runAlgoStmtsWhenEval(instAlgoDef.(*ast.DefAlgoStmt).Stmts, fcFnWithValueParams)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return exec.simplifyNumExprFc(value)
}

func (exec *Executor) runAlgoStmtsWhenEval(algoStmts ast.AlgoStmtSlice, fcFnWithValueParams *ast.FcFn) (ast.Fc, ExecRet) {
	for _, stmt := range algoStmts {
		switch asStmt := stmt.(type) {
		case *ast.AlgoReturnStmt:
			execRet, err := exec.factStmt(ast.EqualFact(fcFnWithValueParams, asStmt.Value))
			if err != nil || execRet.IsNotTrue() {
				return nil, execRet
			}
			numExprFc, execRet := exec.evalFcThenSimplify(asStmt.Value)
			return numExprFc, execRet
		case *ast.AlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsNotTrue() {
				return nil, execRet
			} else if conditionIsTrue {
				return exec.algoIfStmtWhenEval(asStmt, fcFnWithValueParams)
			}
		case *ast.ProveAlgoReturnStmt:
			return nil, NewExecErr(fmt.Sprintf("There can not be return by statements in algo, get %s", asStmt.String()))
		default:
			execRet, _, err := exec.Stmt(stmt.(ast.Stmt))
			if err != nil || execRet.IsNotTrue() {
				return nil, execRet
			}
		}
	}

	return nil, NewExecErr(fmt.Sprintf("There is no return value of %s", fcFnWithValueParams))
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

			if execRet.IsNotTrue() {
				return false, NewExecErr(fmt.Sprintf("%s is unknown. Negation of it is also unknown. Fail to verify condition of if statement:\n%s", fact, stmt))
			}
		}

		return false, NewExecTrue("")
	}

	return true, NewExecTrue("")
}

func (exec *Executor) algoIfStmtWhenEval(stmt *ast.AlgoIfStmt, fcFnWithValueParams *ast.FcFn) (ast.Fc, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnvAndGiveUpMsgs()

	// all conditions are true
	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	execRet := exec.knowStmt(knowStmt)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	value, execRet := exec.runAlgoStmtsWhenEval(stmt.ThenStmts, fcFnWithValueParams)
	return value, execRet
}
