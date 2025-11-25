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
	execState, returnedFacts := exec.callProveAlgo(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	// 保存返回的事实
	for _, fact := range returnedFacts {
		ret := exec.Env.NewFact(fact)
		if ret.IsNotTrue() {
			return NewExecErr(fmt.Sprintf("by statement failed: returned fact %s store error.", fact.String()))
		}
	}

	return NewExecTrue("")
}

// 工作原理是吧ProveAlgoDef的params都变成传入的obj，然后instantiate，然后run
// Returns ExecRet and the facts returned by prove_algo
func (exec *Executor) callProveAlgo(stmt *ast.ByStmt) (ExecRet, []ast.FactStmt) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	proveAlgoDef := exec.Env.GetProveAlgoDef(stmt.ProveAlgoName)
	if proveAlgoDef == nil {
		return NewExecErr(fmt.Sprintf("prove algo %s not found", stmt.ProveAlgoName)), nil
	}

	if len(proveAlgoDef.Params) != len(stmt.Params) {
		return NewExecErr(fmt.Sprintf("prove algo %s requires %d params, get %d instead", stmt.ProveAlgoName, len(proveAlgoDef.Params), len(stmt.Params))), nil
	}

	for i, param := range proveAlgoDef.Params {
		if exec.Env.IsAtomDeclared(ast.AtomObj(param), map[string]struct{}{}) {
			continue
		} else {
			execState := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.AtomObj(glob.KeywordObj)}, []ast.FactStmt{ast.NewEqualFact(ast.AtomObj(param), stmt.Params[i])}, stmt.Line))
			if execState.IsNotTrue() {
				return execState, nil
			}
		}
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range proveAlgoDef.Params {
		uniMap[param] = stmt.Params[i]
	}

	instProveAlgoDef, err := proveAlgoDef.Instantiate(uniMap)
	if err != nil {
		return NewExecErrWithErr(err), nil
	}

	execRet, returnedFacts := exec.runAlgoStmtsWhenBy(instProveAlgoDef.(*ast.DefProveAlgoStmt).Stmts, stmt.Params)
	if execRet.IsNotTrue() {
		return execRet, nil
	}

	return NewExecTrue(""), returnedFacts
}

func (exec *Executor) runAlgoStmtsWhenBy(algoStmts ast.AlgoStmtSlice, paramsValues []ast.Obj) (ExecRet, ast.FactStmtSlice) {
	for _, stmt := range algoStmts {
		switch asStmt := stmt.(type) {
		case *ast.ProveAlgoReturnStmt:
			execRet := exec.runProveAlgoReturnStmt(asStmt)
			if execRet.IsNotTrue() {
				return execRet, nil
			}
			// Return the facts from prove_algo
			return NewExecTrue(""), asStmt.Facts
		case *ast.AlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsErr() {
				return execRet, nil
			} else if conditionIsTrue {
				return exec.algoIfStmtWhenBy(asStmt, paramsValues)
			} else if execRet.IsUnknown() {
				continue
			}
		case *ast.AlgoReturnStmt:
			return NewExecErr(fmt.Sprintf("There can not be return value statements in algo. Use return eval instead .Get %s", asStmt.String())), nil
		default:
			execRet := exec.Stmt(stmt.(ast.Stmt))
			if execRet.IsNotTrue() {
				return execRet, nil
			}
		}
	}
	return NewExecTrue(""), nil
}

func (exec *Executor) algoIfStmtWhenBy(stmt *ast.AlgoIfStmt, paramsValues []ast.Obj) (ExecRet, []ast.FactStmt) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	execRet := exec.knowStmt(knowStmt)
	if execRet.IsNotTrue() {
		return execRet, nil
	}

	return exec.runAlgoStmtsWhenBy(stmt.ThenStmts, paramsValues)
}

func (exec *Executor) runProveAlgoReturnStmt(stmt *ast.ProveAlgoReturnStmt) ExecRet {
	if len(stmt.Facts) == 0 {
		return NewExecTrue("")
	}

	// Verify all returned facts are true
	for _, fact := range stmt.Facts {
		execState := exec.factStmt(fact)
		if execState.IsNotTrue() {
			return execState.AddMsg(fmt.Sprintf("return fact failed: %s", fact.String()))
		}
	}

	return NewExecTrue("")
}
