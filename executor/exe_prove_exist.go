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

	return execState
}

func (exec *Executor) proveExistStmt_Prove(stmt *ast.ProveExistStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	// prove proofs
	for _, proof := range stmt.Proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState
		}
	}

	uniMap := map[string]ast.Obj{}
	for i, equalTo := range stmt.EqualTos {
		curParamSet, err := stmt.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}

		inFact := ast.NewInFactWithObj(equalTo, curParamSet)
		execState := exec.factStmt(inFact)
		if execState.IsNotTrue() {
			return execState
		}

		uniMap[stmt.Params[i]] = equalTo
	}

	uniMap2 := map[string]ast.Obj{}
	for i, equalTo := range stmt.EqualTos {
		uniMap2[stmt.Params[i]] = equalTo
	}

	instFact, err := stmt.Fact.InstantiateFact(uniMap2)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	execState := exec.factStmt(instFact)
	if execState.IsNotTrue() {
		return execState
	}

	return glob.NewEmptyStmtTrue()
}
