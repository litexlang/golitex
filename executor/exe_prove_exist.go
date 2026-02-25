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
)

func (exec *Executor) proveExistStmt(stmt *ast.WitnessStmt) ast.StmtRet {
	// given equal tos are in those
	execState := exec.proveExistStmt_Prove(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	execState = exec.proveExistStmt_NewFact(stmt)
	if execState.IsNotTrue() {
		return execState
	}

	return execState
}

func (exec *Executor) proveExistStmt_Prove(stmt *ast.WitnessStmt) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// prove proofs
	bodyRets := []ast.StmtRet{}
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
		bodyRets = append(bodyRets, execState)
	}

	verProcessRets := []ast.VerRet{}
	// prove in each param set
	uniMap := map[string]ast.Obj{}
	for i, equalTo := range stmt.EqualTos {
		curParamSet, err := stmt.ExistParamSets[i].Instantiate(uniMap)
		if err != nil {
			return ast.StmtErrRet(stmt, err.Error())
		}

		inFact := ast.NewInFactWithObj(equalTo, curParamSet)
		execState := exec.factStmt(inFact)

		if execState.IsNotTrue() {
			return execState
		}

		verProcessRets = append(verProcessRets, execState.GetVerifyProcess()...)

		uniMap[stmt.ExistParams[i]] = equalTo
	}

	for _, fact := range stmt.Fact {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return ast.StmtErrRet(stmt, err.Error())
		}

		execState := exec.factStmt(instFact)
		if execState.IsNotTrue() {
			return execState
		}

		verProcessRets = append(verProcessRets, execState.GetVerifyProcess()...)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses(verProcessRets)
}

func (exec *Executor) proveExistStmt_NewFact(stmt *ast.WitnessStmt) ast.StmtRet {
	newFact := stmt.ToTrueExistStFact()
	ret := exec.Env.NewFactWithCheckingNameDefined(newFact)
	if ret.IsErr() {
		return ast.StmtErrRet(stmt, ret.String())
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddInfers([]ast.InferRet{ret}).AddExtraInfo(newFact.String())
}
