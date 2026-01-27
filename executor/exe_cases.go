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

func (exec *Executor) execCases(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	verifyProcessRet := exec.execCases_Verify(stmt)
	if verifyProcessRet.IsNotTrue() {
		return verifyProcessRet
	}

	newFactRet := exec.execCases_NewFact(stmt)
	if newFactRet.IsNotTrue() {
		return verifyProcessRet
	}

	return exec.NewTrueStmtRet(stmt).AddVerifyProcesses(verifyProcessRet.VerifyProcess).AddNewFacts(newFactRet.NewFact)
}

func (exec *Executor) execCases_NewFact(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	newMsg := []string{}
	for _, thenFact := range stmt.ThenFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(thenFact)
		if ret.IsNotTrue() {
			return ret
		}
		newMsg = append(newMsg, ret.NewFact...)
	}

	return glob.NewEmptyStmtTrue().AddNewFacts(newMsg)
}

func (exec *Executor) execCases_Verify(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	// check cases cover all situations
	ret := exec.execCases_Verify_all_cases_cover_all_situations(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// check case by case
	for i := range len(stmt.CaseFacts) {
		ret = exec.execCases_Verify_case_by_case(stmt, i)
		if ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

func (exec *Executor) execCases_Verify_all_cases_cover_all_situations(stmt *ast.ProveCaseByCaseStmt) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	for _, curStmt := range stmt.ProveCases {
		ret := exec.Stmt(curStmt)
		if ret.IsNotTrue() {
			return ret
		}
	}

	orFact := ast.NewOrStmt(stmt.CaseFacts, glob.BuiltinLine0)
	ret := exec.factStmt(orFact)
	return ret
}

func (exec *Executor) execCases_Verify_case_by_case(stmt *ast.ProveCaseByCaseStmt, index int) *glob.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.CaseFacts[index])
	if ret.IsNotTrue() {
		return ret
	}

	if len(stmt.Proofs[index]) != 0 {
		for i := 0; i < len(stmt.Proofs[index])-1; i++ {
			curStmt := stmt.Proofs[index][i]
			ret = exec.Stmt(curStmt)
			if ret.IsNotTrue() {
				return ret
			}
		}

		lastStmt := stmt.Proofs[index][len(stmt.Proofs[index])-1]

		if impossibleStmt, ok := lastStmt.(*ast.ImpossibleStmt); ok {
			ret = exec.Stmt(impossibleStmt.Fact)
			if ret.IsNotTrue() {
				return ret
			}

			reversedImpossibleFacts := impossibleStmt.Fact.ReverseIsTrue()
			for _, reversed := range reversedImpossibleFacts {
				ret = exec.Stmt(reversed)
				if ret.IsNotTrue() {
					return ret
				}
			}

		} else {
			ret = exec.Stmt(lastStmt)
			if ret.IsNotTrue() {
				return ret
			}
		}

		for _, thenFact := range stmt.ThenFacts {
			ret = exec.Stmt(thenFact)
			if ret.IsNotTrue() {
				return ret
			}
		}
	}

	return glob.NewEmptyStmtTrue()
}
