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

func (exec *Executor) proveExistStmt(stmt *ast.ProveExistStmt) *glob.StmtRet {
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

func (exec *Executor) proveExistStmt_Prove(stmt *ast.ProveExistStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// prove proofs
	bodyRets := []*glob.StmtRet{}
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(bodyRets)
		}
		bodyRets = append(bodyRets, execState)
	}

	verProcessRets := []*glob.VerRet{}
	// prove in each param set
	uniMap := map[string]ast.Obj{}
	for i, equalTo := range stmt.EqualTos {
		curParamSet, err := stmt.ExistParamSets[i].Instantiate(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}

		inFact := ast.NewInFactWithObj(equalTo, curParamSet)
		execState := exec.factStmt(inFact)

		if execState.IsNotTrue() {
			return execState
		}

		verProcessRets = append(verProcessRets, execState.VerifyProcess...)

		uniMap[stmt.ExistParams[i]] = equalTo
	}

	instFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	execState := exec.factStmt(instFact)
	if execState.IsNotTrue() {
		return execState
	}

	verProcessRets = append(verProcessRets, execState.VerifyProcess...)

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verProcessRets)
}

func (exec *Executor) proveExistStmt_NewFact(stmt *ast.ProveExistStmt) *glob.StmtRet {
	newFact := stmt.ToTrueExistStFact()
	ret := exec.Env.NewFactWithoutCheckingNameDefined(newFact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	return glob.NewStmtTrueWithInfers(ret.Infer).AddNewFact(newFact.String())
}
