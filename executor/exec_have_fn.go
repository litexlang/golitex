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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) haveFnStmtCaseByCase(stmt *ast.HaveFnCaseByCaseStmt) *glob.StmtRet {
	ret := exec.haveFnEqualCaseByCase_Verify(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	newRet := exec.haveFnCaseByCase_Define(stmt)
	if newRet.IsNotTrue() {
		return newRet
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(ret.VerifyProcess).AddDefineMsgs(newRet.Define)
}

func (exec *Executor) haveFnEqualCaseByCase_Verify(stmt *ast.HaveFnCaseByCaseStmt) *glob.StmtRet {
	verifyProcessMsgs := []*glob.VerRet{}

	exec.NewEnv()
	defer exec.deleteEnv()

	// 申明所有的param
	newLetStmt := ast.NewDefLetStmt(stmt.DefFnStmt.FnTemplate.Params, stmt.DefFnStmt.FnTemplate.ParamSets, stmt.DefFnStmt.FnTemplate.DomFacts, stmt.Line)
	execState := exec.defLetStmt(newLetStmt)
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}

	verRet := exec.haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSetAndSatisfyThen(stmt)
	if verRet.IsNotTrue() {
		return verRet
	}

	return glob.NewEmptyStmtTrue().AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSetAndSatisfyThen(stmt *ast.HaveFnCaseByCaseStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// 证明 proof
	for _, proof := range stmt.ProveCases {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return glob.ErrRet(execState.String())
		}
	}

	// 证明 or cases 成立
	orFact := ast.NewOrStmt(stmt.CaseByCaseFacts, stmt.Line)
	execState := exec.factStmt(orFact)
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}

	// 证明 cases 互相不冲突且返回值在 retSet里且then fact成立
	for i := range len(stmt.CaseByCaseFacts) {
		execState = exec.haveFnCaseByCaseStmt_CheckCasesNotOverlap_ReturnValueInRetSet(stmt, i)
		if execState.IsNotTrue() {
			return glob.ErrRet(execState.String())
		}
	}

	return exec.NewTrueStmtRet(orFact)
}

func (exec *Executor) haveFnCaseByCaseStmt_CheckCasesNotOverlap_ReturnValueInRetSet(stmt *ast.HaveFnCaseByCaseStmt, index int) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// index known是对的
	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.CaseByCaseFacts[index])
	if ret.IsNotTrue() {
		return glob.ErrRet(ret.String())
	}

	// 其他index的逆都是错的
	for i := range len(stmt.CaseByCaseFacts) {
		if i == index {
			continue
		}
		notOtherCaseFacts := stmt.CaseByCaseFacts[i].ReverseIsTrue()
		for _, notOtherCaseFact := range notOtherCaseFacts {
			execState := exec.factStmt(notOtherCaseFact)
			if execState.IsNotTrue() {
				return glob.ErrRet(execState.String())
			}
		}
	}

	// 跑case proof
	for _, curStmt := range stmt.Proofs[index] {
		ret := exec.Stmt(curStmt)
		if ret.IsNotTrue() {
			return ret
		}
	}

	// 返回值在 retSet里
	inFact := ast.NewInFactWithObj(stmt.EqualToObjs[index], stmt.DefFnStmt.FnTemplate.RetSet)
	ret = exec.factStmt(inFact)
	if ret.IsNotTrue() {
		return glob.ErrRet(ret.String())
	}

	panic("not implemented: 验证 then fact成立。这里可能要得在这里把函数先声明了，约束x在这个case上，然后验证里面的forall")

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveFnCaseByCase_Define(stmt *ast.HaveFnCaseByCaseStmt) *glob.StmtRet {
	defineMsgs := []string{}

	// 定义函数
	newFnDefStmt := ast.NewLetFnStmt(string(stmt.DefFnStmt.Name), stmt.DefFnStmt.FnTemplate, stmt.Line)
	execState := exec.lefDefFnStmt(newFnDefStmt)
	if execState.IsNotTrue() {
		return exec.AddStmtToStmtRet(execState, stmt)
	}
	defineMsgs = append(defineMsgs, newFnDefStmt.String())

	return glob.NewEmptyStmtTrue().AddDefineMsgs(defineMsgs)
}
