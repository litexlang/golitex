package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) haveFnEqualCaseByCaseStmt2(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
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
	verifyProcessMsgs := []*glob.VerRet{}

	exec.NewEnv()
	defer exec.deleteEnv()

	// 申明所有的param
	newLetStmt := ast.NewDefLetStmt(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []ast.FactStmt{}, stmt.Line)
	execState := exec.defLetStmt(newLetStmt)
	if execState.IsNotTrue() {
		return glob.ErrRet(execState.String())
	}

	verRet := exec.haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap(stmt)
	if verRet.IsNotTrue() {
		return verRet
	}

	return glob.NewEmptyStmtTrue().AddVerifyProcesses(verifyProcessMsgs)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_CheckAllCasesCoverDomain_CasesNoOverlap(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
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
		execState = exec.haveFnEqualCaseByCaseStmt_CheckCasesNotOverlap(stmt, i)
		if execState.IsNotTrue() {
			return glob.ErrRet(execState.String())
		}
	}

	return exec.NewTrueStmtRet(orFact)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_CheckCasesNotOverlap(stmt *ast.HaveFnEqualCaseByCaseStmt, index int) *glob.StmtRet {
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

	return exec.NewTrueStmtRet(stmt)
}

func (exec *Executor) haveFnEqualCaseByCaseStmt_Define(stmt *ast.HaveFnEqualCaseByCaseStmt) *glob.StmtRet {
	defineMsgs := []string{}
	thenFacts := []ast.FactStmt{}
	for i, caseFact := range stmt.CaseByCaseFacts {
		// 在 caseFact 的条件下，函数值等于对应的返回值
		// 需要将 caseFact 作为条件，然后添加等式
		fnCall := fnHeaderToReturnValueOfFn(stmt.DefHeader)
		equalFact := ast.NewEqualFact(fnCall, stmt.CaseByCaseEqualTo[i])

		// 创建一个条件事实：如果 caseFact 为真，则 equalFact 为真
		// 这里我们需要使用 implication 或者直接在 thenFacts 中添加条件
		// 由于 caseFact 是 SpecFactStmt，我们需要创建一个 UniFact 来表示这个条件
		// 但是更简单的方式是：创建一个 UniFact，其中 DomFacts 包含 caseFact，ThenFacts 包含 equalFact
		uniFact := ast.NewUniFact(
			[]string{},
			[]ast.Obj{},
			[]ast.FactStmt{caseFact},
			[]ast.FactStmt{equalFact},
			stmt.Line,
		)
		thenFacts = append(thenFacts, uniFact)
	}

	// 定义函数
	newFnDefStmt := ast.NewLetFnStmt(
		string(stmt.DefHeader.Name),
		ast.NewFnTStruct(
			stmt.DefHeader.Params,
			stmt.DefHeader.ParamSets,
			stmt.RetSet,
			[]ast.FactStmt{},
			thenFacts,
			stmt.Line,
		),
		stmt.Line,
	)
	execState := exec.lefDefFnStmt(newFnDefStmt)
	if execState.IsNotTrue() {
		return exec.AddStmtToStmtRet(execState, stmt)
	}
	defineMsgs = append(defineMsgs, newFnDefStmt.String())
	return glob.NewEmptyStmtTrue().AddDefineMsgs(defineMsgs)
}
