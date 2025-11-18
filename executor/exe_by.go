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
	glob "golitex/glob"
)

func (exec *Executor) byStmt(stmt *ast.ByStmt) ExecRet {
	if len(stmt.ThenFactsOrNil) > 0 {
		exec.NewEnv(exec.Env)
		defer exec.deleteEnv()
	}

	execState := exec.callProveAlgo(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	if len(stmt.ThenFactsOrNil) > 0 {
		for _, fact := range stmt.ThenFactsOrNil {
			execState := exec.factStmt(fact)
			if execState.IsErr() {
				return NewExecErr("")
			}
			if execState.IsNotTrue() {
				return execState
			}
		}
	}

	return NewExecTrue("")
}

// 工作原理是吧ProveAlgoDef的params都变成传入的obj，然后instantiate，然后run
func (exec *Executor) callProveAlgo(stmt *ast.ByStmt) ExecRet {
	proveAlgoDef := exec.Env.GetProveAlgoDef(stmt.ProveAlgoName)
	if proveAlgoDef == nil {
		return NewExecErr(fmt.Sprintf("prove algo %s not found", stmt.ProveAlgoName))
	}

	if len(proveAlgoDef.Params) != len(stmt.Params) {
		return NewExecErr(fmt.Sprintf("prove algo %s requires %d params, get %d instead", stmt.ProveAlgoName, len(proveAlgoDef.Params), len(stmt.Params)))
	}

	for i, param := range proveAlgoDef.Params {
		if exec.Env.IsAtomDeclared(ast.AtomObj(param), map[string]struct{}{}) {
			continue
		} else {
			execState := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.AtomObj(glob.KeywordObj)}, []ast.FactStmt{ast.NewEqualFact(ast.AtomObj(param), stmt.Params[i])}, stmt.Line))
			if execState.IsNotTrue() {
				return execState
			}
		}
	}

	// params of stmt must be numeric literals
	// paramsValues := []ast.Fc{}
	// for _, param := range stmt.Params {
	// 	value, execRet := exec.verifyIsNumExprFcOrHasValueThenSimplify(param)
	// 	if execRet.IsNotTrue() {
	// 		return execRet
	// 	}
	// 	paramsValues = append(paramsValues, value)
	// }

	uniMap := map[string]ast.Obj{}
	for i, param := range proveAlgoDef.Params {
		uniMap[param] = stmt.Params[i]
	}

	instProveAlgoDef, err := proveAlgoDef.Instantiate(uniMap)
	if err != nil {
		return NewExecErrWithErr(err)
	}

	execRet := exec.runAlgoStmtsWhenBy(instProveAlgoDef.(*ast.DefProveAlgoStmt).Stmts, stmt.Params)
	if execRet.IsNotTrue() {
		return execRet
	}

	return NewExecTrue("")
}

// func (exec *Executor) verifyIsNumExprFcOrHasValueThenSimplify(fc ast.Fc) (ast.Fc, ExecRet) {
// 	if cmp.IsNumLitFc(fc) {
// 		return exec.simplifyNumExprFc(fc)
// 	}

// 	value := exec.Env.GetSymbolSimplifiedValue(fc)
// 	if value == nil {
// 		return nil, NewExecErr(fmt.Sprintf("symbol %s has no value", fc.String()))
// 	}

// 	return value, NewExecTrue("")
// }

func (exec *Executor) runAlgoStmtsWhenBy(algoStmts ast.AlgoStmtSlice, paramsValues []ast.Obj) ExecRet {
	for _, stmt := range algoStmts {
		switch asStmt := stmt.(type) {
		case *ast.ProveAlgoReturnStmt:
			return exec.runProveAlgoReturnStmt(asStmt)
		case *ast.AlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsNotTrue() {
				return execRet
			} else if conditionIsTrue {
				return exec.algoIfStmtWhenBy(asStmt, paramsValues)
			}
		case *ast.AlgoReturnStmt:
			return NewExecErr(fmt.Sprintf("There can not be return value statements in algo. Use return eval instead .Get %s", asStmt.String()))
		default:
			execRet := exec.Stmt(stmt.(ast.Stmt))
			if execRet.IsNotTrue() {
				return execRet
			}
		}
	}
	return NewExecTrue("")
}

func (exec *Executor) algoIfStmtWhenBy(stmt *ast.AlgoIfStmt, paramsValues []ast.Obj) ExecRet {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	execRet := exec.knowStmt(knowStmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	return exec.runAlgoStmtsWhenBy(stmt.ThenStmts, paramsValues)
}

func (exec *Executor) runProveAlgoReturnStmt(stmt *ast.ProveAlgoReturnStmt) ExecRet {
	if stmt.ByStmtOrNil == nil {
		return NewExecTrue("")
	}

	execState := exec.callProveAlgo(ast.NewByStmt(stmt.ByStmtOrNil.ProveAlgoName, stmt.ByStmtOrNil.Params, stmt.ByStmtOrNil.ThenFactsOrNil, stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}

	return NewExecTrue("")
}
