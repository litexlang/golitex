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

func (exec *Executor) haveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
	ret := exec.haveFnEqualCaseByCaseStmt_Verify(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	newRet := exec.haveFnEqualCaseByCaseStmt_Define(stmt)
	if newRet.IsNotTrue() {
		return newRet
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(ret.VerifyProcess).AddDefineMsgs(newRet.Define)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_Verify(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
	verifyProcessMsgs := []VerRet{}

	exec.NewEnv()
	defer exec.deleteEnv()

	// 申明所有的param
	newLetStmt := ast.NewDefLetStmt(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []ast.FactStmt{}, stmt.Line)
	execState := exec.defLetStmt(newLetStmt)
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}

	verRet := exec.haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSet(stmt)
	if verRet.IsNotTrue() {
		return verRet
	}

	return glob.NewEmptyStmtTrue().AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap_ReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
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

	// 证明 cases 互相不冲突
	for i := range len(stmt.CaseByCaseFacts) {
		execState = exec.haveFnEqualCaseByCaseStmt_CheckCasesNotOverlap_ReturnValueInRetSet(stmt, i)
		if execState.IsNotTrue() {
			return glob.ErrRet(execState.String())
		}
	}

	return exec.NewTrueStmtRet(orFact)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_CheckCasesNotOverlap_ReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCaseStmt, index int) *glob.StmtRet {
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
	inFact := ast.NewInFactWithObj(stmt.CaseByCaseEqualTo[index], stmt.RetSet)
	ret = exec.factStmt(inFact)
	if ret.IsNotTrue() {
		return ret
	}

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_Define(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
	anonymousSetTheFnIsIn := ast.NewAnonymousFnSetObj(stmt.DefHeader.ParamSets, stmt.RetSet)
	defFn := ast.NewDefLetStmt([]string{stmt.DefHeader.Name}, []ast.Obj{anonymousSetTheFnIsIn}, []ast.FactStmt{}, stmt.Line)
	defRet := exec.defLetStmt(defFn)
	if defRet.IsNotTrue() {
		return exec.AddStmtToStmtRet(defRet, stmt)
	}

	curFnObjParams := []ast.Obj{}
	for _, paramSet := range stmt.DefHeader.Params {
		curFnObjParams = append(curFnObjParams, ast.Atom(paramSet))
	}
	curFnObj := ast.NewFnObj(ast.Atom(stmt.DefHeader.Name), curFnObjParams)

	infers := []string{}
	for i, curCase := range stmt.CaseByCaseFacts {
		uniFact := ast.NewUniFact(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []ast.Spec_OrFact{curCase}, []ast.Spec_OrFact{ast.NewEqualFact(curFnObj, stmt.CaseByCaseEqualTo[i])}, curCase.GetLine())
		ret := exec.Env.NewFactWithCheckingNameDefined(uniFact)
		if ret.IsNotTrue() {
			return ret
		}
		infers = append(infers, uniFact.String())
	}

	return exec.AddStmtToStmtRet(defRet.AddInfers(infers), stmt)
}
