// Copyright Jiachen Shen.
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
	"errors"
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (exec *Executor) simplifyNumExprObj(obj ast.Obj) (ast.Obj, error) {
	simplifiedNumExprObj := cmp.IsNumExprObjThenSimplify(obj)
	if simplifiedNumExprObj == nil {
		return nil, errors.New("simplify num expr obj failed")
	}

	return simplifiedNumExprObj, nil
}

// 这里 bool 表示，是否启动过 用algo 计算；如果仅仅是用 algo 来计算，那是不会返回true的
func (exec *Executor) evalObjThenSimplify(obj ast.Obj) (ast.Obj, ast.StmtRet) {
	// fmt.Println(obj)

	if cmp.IsNumExprLitObj(obj) {
		simplifiedNumExprObj, err := exec.simplifyNumExprObj(obj)
		if err != nil {
			return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0)).AddExtraInfo(err.Error())
		}
		return simplifiedNumExprObj, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0))
	}

	switch asObj := obj.(type) {
	case ast.Atom:
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("symbol %s has no value", obj.String()))
	case *ast.FnObj:
		return exec.evalFnObjThenSimplify(asObj)
	default:
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("unexpected type: %T", obj))
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
func (exec *Executor) evalFnObjThenSimplify(fnObj *ast.FnObj) (ast.Obj, ast.StmtRet) {
	// if symbolValue := exec.Env.GetSymbolSimplifiedValue(fnObj); symbolValue != nil {
	// 	return symbolValue, glob.NewEmptyStmtTrue()
	// }

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
			return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("%s = %s is invalid", fnObj, numExprObj))
		}

		obj, err := exec.simplifyNumExprObj(numExprObj)
		if err != nil {
			return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(err.Error())
		}
		return obj, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0))
	}

	if ok := exec.Env.IsFnWithDefinedAlgo(fnObj); ok {
		numExprObj, execRet := exec.useAlgoToEvalFnObjThenSimplify(fnObj)
		if execRet.IsNotTrue() {
			return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("failed to use algo to evaluate %s", fnObj))
		}

		return numExprObj, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0))
	}

	return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo("failed to evaluate fn obj")
}

func (exec *Executor) useAlgoToEvalFnObjThenSimplify(fnObj *ast.FnObj) (ast.Obj, ast.StmtRet) {
	algoDef := exec.Env.GetAlgoDef(fnObj.FnHead.String())
	if algoDef == nil {
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("algo %s is not found", fnObj.FnHead.String()))
	}

	if len(fnObj.Params) != len(algoDef.Params) {
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("algorithm %s requires %d parameters, get %d instead", algoDef.FuncName, len(algoDef.Params), len(fnObj.Params)))
	}

	// 传入的参数真的在fn的domain里
	execRet := exec.fnObjParamsInFnDomain(fnObj)
	if execRet.IsNotTrue() {
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("parameters of %s are not in domain of %s", fnObj, fnObj.FnHead))
	}

	fnObjParamsValues := []ast.Obj{}
	for _, param := range fnObj.Params {
		_, value := exec.Env.GetStoredSymbolValue(param)
		// simplifiedValue := value
		simplifiedValue, err := exec.simplifyNumExprObj(value)
		if err != nil {
			return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("value of %s of %s is unknown.", param, fnObj))
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
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(err.Error())
	}

	value, execRet := exec.runAlgoStmtsWhenEval(instAlgoDef.(*ast.DefAlgoStmt).Stmts, fnObjWithValueParams)
	if execRet.IsNotTrue() {
		return nil, execRet
	}

	simplifiedValue, err := exec.simplifyNumExprObj(value)
	if err != nil {
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0)).AddExtraInfo(err.Error())
	}
	return simplifiedValue, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(fnObj, glob.BuiltinLine0))
}

// 如果是 return，那返回 obj
// 如果是 if，那 如果condition 满足了，就返回 if 里的 return value；如果是 condition 不满足，那返回 nil
func (exec *Executor) runAlgoIfAlgoReturn(stmt ast.AlgoIfAlgoReturn, fnObjWithValueParams *ast.FnObj) (ast.Obj, ast.StmtRet) {
	switch asStmt := stmt.(type) {
	case *ast.AlgoReturn:
		ver := NewVerifier(exec.Env)
		execRet := ver.VerFactStmt(ast.EqualFact(fnObjWithValueParams, asStmt.Value), Round0NoMsg())
		if execRet.IsNotTrue() {
			return nil, execRet.ToStmtRet()
		}

		if cmp.IsNumExprLitObj(asStmt.Value) {
			return asStmt.Value, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(asStmt.Value, glob.BuiltinLine0))
		}

		numExprObj, ret := exec.evalObjThenSimplify(asStmt.Value)
		return numExprObj, ret
	case *ast.AlgoIf:
		if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsNotTrue() {
			return nil, ast.NewTrueStmtEmptyRet(nil)
		} else if conditionIsTrue {
			return exec.algoIfStmtWhenEval(asStmt, fnObjWithValueParams)
		}
	default:
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObjWithValueParams, glob.BuiltinLine0)).AddExtraInfo(fmt.Sprintf("unknown algo if algo return type: %T", asStmt))
	}

	return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObjWithValueParams, glob.BuiltinLine0)).AddExtraInfo("unknown algo if algo return type")
}

// 要做到这样的效果：每一步只是做验证，所以不应该有中间过程被know下来
func (exec *Executor) runAlgoStmtsWhenEval(algoStmts ast.AlgoIfAlgoReturnSlice, fnObjWithValueParams *ast.FnObj) (ast.Obj, ast.StmtRet) {
	for _, stmt := range algoStmts {
		value, execRet := exec.runAlgoIfAlgoReturn(stmt, fnObjWithValueParams)
		if execRet.IsNotTrue() {
			return nil, execRet
		}
		if value != nil {
			return value, execRet
		}
	}

	return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(fnObjWithValueParams, glob.BuiltinLine0)).AddExtraInfo("There is no return value of algoStmts")
}

func (exec *Executor) fnObjParamsInFnDomain(fnObj *ast.FnObj) ast.StmtRet {
	ver := NewVerifier(exec.Env)
	// return ver.objIsDefinedAtomOrIsFnSatisfyItsReq(fnObj, Round0NoMsg()).ToStmtRet()
	return ver.objSatisfyFnReq(fnObj, Round0NoMsg()).ToStmtRet()
}

func (exec *Executor) IsAlgoIfConditionTrue(stmt *ast.AlgoIf) (bool, ast.StmtRet) {
	ver := NewVerifier(exec.Env)
	execRet := ver.VerFactStmt(stmt.Condition, Round0NoMsg()).ToStmtRet()
	return execRet.IsTrue(), execRet
}

func (exec *Executor) algoIfStmtWhenEval(stmt *ast.AlgoIf, fnObjWithValueParams *ast.FnObj) (ast.Obj, ast.StmtRet) {
	// all conditions are true
	// knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	// execRet := exec.knowStmt(knowStmt)
	// if execRet.IsNotTrue() {
	// 	return nil, execRet
	// }

	value, execRet := exec.runAlgoIfAlgoReturn(stmt.ReturnStmt, fnObjWithValueParams)
	return value, execRet
}

func (exec *Executor) GetSimplifiedValue(obj ast.Obj) (ast.Obj, ast.StmtRet) {
	_, value := exec.Env.GetStoredSymbolValue(obj)
	simplifiedValue, err := exec.simplifyNumExprObj(value)
	if err != nil {
		return nil, ast.NewErrStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0)).AddExtraInfo(err.Error())
	}
	return simplifiedValue, ast.NewTrueStmtEmptyRet(ast.NewEvalStmt(obj, glob.BuiltinLine0))
}
