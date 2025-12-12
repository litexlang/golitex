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

func (exec *Executor) simplifyNumExprObj(obj ast.Obj) (ast.Obj, ExecRet) {
	simplifiedNumExprObj := cmp.IsNumExprObjThenSimplify(obj)
	if simplifiedNumExprObj == nil {
		return nil, NewEmptyExecErr()
	}

	return simplifiedNumExprObj, NewEmptyExecTrue()
}

// 这里 bool 表示，是否启动过 用algo 计算；如果仅仅是用 algo 来计算，那是不会返回true的
func (exec *Executor) evalObjThenSimplify(obj ast.Obj) (ast.Obj, ExecRet) {
	// fmt.Println(obj)

	if cmp.IsNumExprLitObj(obj) {
		return exec.simplifyNumExprObj(obj)
	}

	switch asObj := obj.(type) {
	case ast.Atom:
		symbolValue := exec.Env.GetSymbolSimplifiedValue(obj)
		if symbolValue == nil {
			return nil, NewExecErr(fmt.Sprintf("symbol %s has no value", obj.String()))
		}
		return symbolValue, NewEmptyExecTrue()
	case *ast.FnObj:
		return exec.evalFnObjThenSimplify(asObj)
	default:
		return nil, NewExecErr(fmt.Sprintf("unexpected type: %T", obj))
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
func (exec *Executor) evalFnObjThenSimplify(fnObj *ast.FnObj) (ast.Obj, ExecRet) {
	if symbolValue := exec.Env.GetSymbolSimplifiedValue(fnObj); symbolValue != nil {
		return symbolValue, NewEmptyExecTrue()
	}

	if ast.IsFn_WithHeadNameInSlice(fnObj, basicArithOptMap) {
		left, execRet := exec.evalObjThenSimplify(fnObj.Params[0])
		if execRet.IsNotTrue() {
			return nil, execRet
		}
		right, execRet := exec.evalObjThenSimplify(fnObj.Params[1])
		if execRet.IsNotTrue() {
			return nil, execRet
		}

		numExprObj := ast.NewFnObj(fnObj.FnHead, []ast.Obj{left, right})
		execRet = exec.fnObjParamsInFnDomain(numExprObj)
		if execRet.IsNotTrue() {
			return nil, NewExecErr(fmt.Sprintf("%s = %s is invalid", fnObj, numExprObj))
		}

		return exec.simplifyNumExprObj(numExprObj)
	}

	if ok := exec.Env.IsFnWithDefinedAlgo(fnObj); ok {
		numExprObj, execRet := exec.useAlgoToEvalFnObjThenSimplify(fnObj)
		if execRet.IsNotTrue() {
			return nil, execRet
		}

		return numExprObj, NewEmptyExecTrue()
	}

	return nil, NewEmptyExecUnknown()
}

func (exec *Executor) useAlgoToEvalFnObjThenSimplify(fnObj *ast.FnObj) (ast.Obj, ExecRet) {
	algoDef := exec.Env.GetAlgoDef(fnObj.FnHead.String())
	if algoDef == nil {
		return nil, NewExecErr(fmt.Sprintf("algo %s is not found", fnObj.FnHead.String()))
	}

	if len(fnObj.Params) != len(algoDef.Params) {
		return nil, NewExecErr(fmt.Sprintf("algorithm %s requires %d parameters, get %d instead", algoDef.FuncName, len(algoDef.Params), len(fnObj.Params)))
	}

	// 传入的参数真的在fn的domain里
	execRet := exec.fnObjParamsInFnDomain(fnObj)
	if execRet.IsNotTrue() {
		return nil, NewExecErr(fmt.Sprintf("parameters of %s are not in domain of %s", fnObj, fnObj.FnHead))
	}

	for i, param := range algoDef.Params {
		ret := exec.Env.IsAtomDeclared(ast.Atom(param), map[string]struct{}{})
		if ret.IsTrue() {
			continue
		} else {
			execState := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{ast.NewEqualFact(ast.Atom(param), fnObj.Params[i])}, glob.BuiltinLine))
			if execState.IsNotTrue() {
				return nil, NewExecErr(execState.String())
			}
		}
	}

	fnObjParamsValues := []ast.Obj{}
	for _, param := range fnObj.Params {
		_, value := exec.Env.ReplaceSymbolWithValue(param)
		// simplifiedValue := value
		simplifiedValue, execRet := exec.simplifyNumExprObj(value)
		if execRet.IsNotTrue() {
			return nil, NewExecErr(fmt.Sprintf("value of %s of %s is unknown.", param, fnObj))
		}
		fnObjParamsValues = append(fnObjParamsValues, simplifiedValue)
	}

	fnObjWithValueParams := ast.NewFnObj(fnObj.FnHead, fnObjParamsValues)

	uniMap := map[string]ast.Obj{}
	for i, param := range algoDef.Params {
		uniMap[param] = fnObjParamsValues[i]
	}

	instAlgoDef, err := algoDef.Instantiate(uniMap)
	if err != nil {
		return nil, NewExecErrWithErr(err)
	}

	value, execRet := exec.runAlgoStmtsWhenEval(instAlgoDef.(*ast.DefAlgoStmt).Stmts, fnObjWithValueParams)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	return exec.simplifyNumExprObj(value)
}

func (exec *Executor) runAlgoStmtsWhenEval(algoStmts ast.AlgoStmtSlice, fnObjWithValueParams *ast.FnObj) (ast.Obj, ExecRet) {
	for _, stmt := range algoStmts {
		switch asStmt := stmt.(type) {
		case *ast.AlgoReturnStmt:
			execRet := exec.factStmt(ast.EqualFact(fnObjWithValueParams, asStmt.Value))
			if execRet.IsErr() {
				return nil, execRet
			}
			if execRet.IsNotTrue() {
				return nil, execRet
			}
			numExprObj, execRet := exec.evalObjThenSimplify(asStmt.Value)
			return numExprObj, execRet
		case *ast.AlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsNotTrue() {
				return nil, execRet
			} else if conditionIsTrue {
				return exec.algoIfStmtWhenEval(asStmt, fnObjWithValueParams)
			}
		default:
			execRet := exec.Stmt(stmt.(ast.Stmt))
			if execRet.IsNotTrue() {
				return nil, execRet
			}
		}
	}

	return nil, NewExecErr(fmt.Sprintf("There is no return value of %s", fnObjWithValueParams))
}

func (exec *Executor) fnObjParamsInFnDomain(fnObj *ast.FnObj) ExecRet {
	ver := NewVerifier(exec.Env)
	return ver.objIsDefinedAtomOrIsFnSatisfyItsReq(fnObj, Round0NoMsg)
}

func (exec *Executor) IsAlgoIfConditionTrue(stmt *ast.AlgoIfStmt) (bool, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	for _, fact := range stmt.Conditions {
		execRet := exec.factStmt(fact)
		if execRet.IsErr() {
			return false, execRet
		}

		if execRet.IsTrue() {
			continue
		}

		factAsReversibleFact, reversed := fact.(ast.Spec_OrFact)
		if !reversed {
			return false, NewExecErr(fmt.Sprintf("The condition %s in\n%s\nis unknown, and it can not be negated. Failed", fact, stmt))
		}

		for _, reversedFact := range factAsReversibleFact.ReverseIsTrue() {
			execRet := exec.factStmt(reversedFact)
			if execRet.IsErr() {
				return false, execRet
			}

			if execRet.IsNotTrue() {
				return false, NewExecErr(fmt.Sprintf("%s is unknown. Negation of it is also unknown. Fail to verify condition of if statement:\n%s", fact, stmt))
			}
		}

		return false, NewEmptyExecTrue()
	}

	return true, NewEmptyExecTrue()
}

func (exec *Executor) algoIfStmtWhenEval(stmt *ast.AlgoIfStmt, fnObjWithValueParams *ast.FnObj) (ast.Obj, ExecRet) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	// all conditions are true
	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	execRet := exec.knowStmt(knowStmt)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	value, execRet := exec.runAlgoStmtsWhenEval(stmt.ThenStmts, fnObjWithValueParams)
	return value, execRet
}

func (exec *Executor) GetSimplifiedValue(obj ast.Obj) (ast.Obj, ExecRet) {
	_, value := exec.Env.ReplaceSymbolWithValue(obj)
	simplifiedValue, execRet := exec.simplifyNumExprObj(value)
	if execRet.IsNotTrue() {
		return nil, execRet
	}
	return simplifiedValue, execRet
}
