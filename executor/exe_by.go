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
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) byStmt(stmt *ast.ByStmt) *glob.StmtRet {
	execState, returnedFacts := exec.callProveAlgo(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	// 保存返回的事实
	for _, fact := range returnedFacts {
		ret := exec.Env.NewFactWithoutCheckingNameDefined(fact)
		if ret.IsNotTrue() {
			return glob.ErrRet(fmt.Sprintf("by statement failed: returned fact %s store error.", fact.String()))
		}
	}

	return glob.NewEmptyStmtTrue()
}

// 工作原理是吧ProveAlgoDef的params都变成传入的obj，然后instantiate，然后run
// Returns *glob.GlobRet and the FactStmt slice returned by prove_algo
// If a ByStmt is encountered, it recursively extracts facts from it
func (exec *Executor) callProveAlgo(stmt *ast.ByStmt) (*glob.StmtRet, []ast.FactStmt) {
	exec.NewEnv()
	defer exec.deleteEnv()

	proveAlgoDef := exec.Env.GetProveAlgoDef(stmt.ProveAlgoName)
	if proveAlgoDef == nil {
		return glob.ErrRet(fmt.Sprintf("prove algo %s not found", stmt.ProveAlgoName)), nil
	}

	if len(proveAlgoDef.Params) != len(stmt.Params) {
		return glob.ErrRet(fmt.Sprintf("prove algo %s requires %d params, get %d instead", stmt.ProveAlgoName, len(proveAlgoDef.Params), len(stmt.Params))), nil
	}

	for i, param := range proveAlgoDef.Params {
		ret := exec.Env.IsNameUnavailable(param, map[string]struct{}{})
		if ret.IsTrue() {
			continue
		} else {
			execState := exec.defLetStmt(ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordSet)}, []ast.FactStmt{ast.NewEqualFact(ast.Atom(param), stmt.Params[i])}, stmt.Line))
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
		return glob.ErrRetWithErr(err), nil
	}

	execRet, returnedFacts := exec.runProveAlgoStmtsWhenBy(instProveAlgoDef.(*ast.DefProveAlgoStmt).Stmts, stmt.Params)
	if execRet.IsNotTrue() {
		return execRet, nil
	}

	return glob.NewEmptyStmtTrue(), returnedFacts
}

func (exec *Executor) runProveAlgoStmtsWhenBy(proveAlgoStmts ast.ProveAlgoStmtSlice, paramsValues []ast.Obj) (*glob.StmtRet, []ast.FactStmt) {
	for _, stmt := range proveAlgoStmts {
		switch asStmt := stmt.(type) {
		case *ast.ProveAlgoReturnStmt:
			execRet, facts := exec.runProveAlgoReturnStmt(asStmt)
			if execRet.IsNotTrue() {
				return execRet, nil
			}
			// Return the facts from prove_algo
			return glob.NewEmptyStmtTrue(), facts
		case *ast.ProveAlgoIfStmt:
			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(ast.NewAlgoIfStmt(asStmt.Conditions, nil, asStmt.Line)); execRet.IsErr() {
				return execRet, nil
			} else if conditionIsTrue {
				return exec.proveAlgoIfStmt(asStmt, paramsValues)
			} else if execRet.IsUnknown() {
				continue
			}
		default:
			return glob.ErrRet(fmt.Sprintf("unexpected prove_algo statement type: %T", stmt)), nil
		}
	}
	return glob.NewEmptyStmtTrue(), nil
}

// func (exec *Executor) runAlgoStmtsWhenBy(algoStmts ast.AlgoStmtSlice, paramsValues []ast.Obj) (*glob.GlobRet, []ast.FactStmt) {
// 	for _, stmt := range algoStmts {
// 		switch asStmt := stmt.(type) {
// 		case *ast.AlgoIfStmt:
// 			if conditionIsTrue, execRet := exec.IsAlgoIfConditionTrue(asStmt); execRet.IsErr() {
// 				return execRet, nil
// 			} else if conditionIsTrue {
// 				return exec.algoIfStmtWhenBy(asStmt, paramsValues)
// 			} else if execRet.IsUnknown() {
// 				continue
// 			}
// 		case *ast.AlgoReturnStmt:
// 			return glob.ErrRet(fmt.Sprintf("There can not be return value statements in algo. Use return eval instead .Get %s", asStmt.String())), nil
// 		default:
// 			execRet := exec.Stmt(stmt.(ast.Stmt))
// 			if execRet.IsNotTrue() {
// 				return execRet, nil
// 			}
// 		}
// 	}
// 	return glob.NewEmptyGlobTrue(), nil
// }

func (exec *Executor) proveAlgoIfStmt(stmt *ast.ProveAlgoIfStmt, paramsValues []ast.Obj) (*glob.StmtRet, []ast.FactStmt) {
	exec.NewEnv()
	defer exec.deleteEnv()

	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
	execRet := exec.knowStmt(knowStmt)
	if execRet.IsNotTrue() {
		return execRet, nil
	}

	return exec.runProveAlgoStmtsWhenBy(stmt.ThenStmts, paramsValues)
}

// func (exec *Executor) algoIfStmtWhenBy(stmt *ast.AlgoIfStmt, paramsValues []ast.Obj) (*glob.GlobRet, []ast.FactStmt) {
// 	exec.NewEnv()
// 	defer exec.deleteEnv()

// 	knowStmt := ast.NewKnowStmt(stmt.Conditions.ToCanBeKnownStmtSlice(), stmt.GetLine())
// 	execRet := exec.knowStmt(knowStmt)
// 	if execRet.IsNotTrue() {
// 		return execRet, nil
// 	}

// 	return exec.runAlgoStmtsWhenBy(stmt.ThenStmts, paramsValues)
// }

func (exec *Executor) runProveAlgoReturnStmt(stmt *ast.ProveAlgoReturnStmt) (*glob.StmtRet, []ast.FactStmt) {
	if len(stmt.Facts) == 0 {
		return glob.NewEmptyStmtTrue(), nil
	}

	resultFacts := []ast.FactStmt{}

	// Process all returned FactOrByStmt
	for _, factOrBy := range stmt.Facts {
		switch item := factOrBy.(type) {
		case ast.FactStmt:
			// 如果是事实，验证是否为真
			execState := exec.factStmt(item)
			if execState.IsNotTrue() {
				return execState.AddError(fmt.Sprintf("return fact failed: %s", item.String())), nil
			}
			// 验证通过后，加入结果列表
			resultFacts = append(resultFacts, item)
		case *ast.ByStmt:
			// 如果是 ByStmt，递归调用 callProveAlgo 来提取事实
			execState, facts := exec.callProveAlgo(item)
			if execState.IsNotTrue() {
				return execState.AddError(fmt.Sprintf("return by statement failed: %s", item.String())), nil
			}
			// 将递归获取的事实加入结果列表
			resultFacts = append(resultFacts, facts...)
		default:
			return glob.ErrRet(fmt.Sprintf("return unexpected type: %T", factOrBy)), nil
		}
	}

	return glob.NewEmptyStmtTrue(), resultFacts
}
