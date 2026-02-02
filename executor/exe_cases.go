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

func (exec *Executor) execCases(stmt *ast.ProveCaseByCaseStmt) ast.StmtRet {
	verifyProcessRet, ok := exec.execCases_Verify(stmt)
	if !ok {
		return ast.NewErrStmtEmptyRet(stmt).AddVerifyProcesses(verifyProcessRet)
	}

	newFactRet, ok := exec.execCases_NewFact(stmt)
	if !ok {
		return ast.NewErrStmtEmptyRet(stmt).AddInfers(newFactRet)
	}

	return ast.NewTrueStmtEmptyRet(stmt).AddVerifyProcesses(verifyProcessRet).AddInfers(newFactRet)
}

func (exec *Executor) execCases_NewFact(stmt *ast.ProveCaseByCaseStmt) ([]ast.InferRet, bool) {
	newInferRetSlice := []ast.InferRet{}
	for _, thenFact := range stmt.ThenFacts {
		ret := exec.Env.NewFactWithCheckingNameDefined(thenFact)
		if ret.IsNotTrue() {
			newInferRetSlice = append(newInferRetSlice, ast.NewErrInferRet(thenFact))
			return newInferRetSlice, false
		}
		newInferRetSlice = append(newInferRetSlice, ret)
	}

	return newInferRetSlice, true
}

func (exec *Executor) execCases_Verify(stmt *ast.ProveCaseByCaseStmt) ([]ast.VerRet, bool) {
	retSlice := []ast.VerRet{}

	// check cases cover all situations
	ret := exec.execCases_Verify_all_cases_cover_all_situations(stmt)
	if ret.IsNotTrue() {
		// or fact
		orFact := ast.NewOrStmt(stmt.CaseFacts, glob.BuiltinLine0)
		retSlice = append(retSlice, ast.NewErrVerRet(orFact))
		return retSlice, false
	}

	// check case by case
	for i := range len(stmt.CaseFacts) {
		ret = exec.execCases_Verify_case_by_case(stmt, i)
		if ret.IsNotTrue() {
			return []ast.VerRet{ast.NewErrVerRet(stmt.CaseFacts[i]).AddExtraInfo(fmt.Sprintf("failed to execute proof for case %d", i)).AddExtraInfos(ret.GetExtraInfos())}, false
		}
		retSlice = append(retSlice, ast.NewErrVerRet(stmt.CaseFacts[i]))
	}

	return retSlice, true
}

func (exec *Executor) execCases_Verify_all_cases_cover_all_situations(stmt *ast.ProveCaseByCaseStmt) ast.StmtRet {
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

func (exec *Executor) execCases_Verify_case_by_case(stmt *ast.ProveCaseByCaseStmt, index int) ast.StmtRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	ret := exec.Env.NewFactWithCheckingNameDefined(stmt.CaseFacts[index])
	if ret.IsNotTrue() {
		return ast.NewErrStmtEmptyRet(stmt.CaseFacts[index]).AddExtraInfo(fmt.Sprintf("failed to store new fact %s", stmt.CaseFacts[index].String()))
	}

	if len(stmt.Proofs[index]) != 0 {
		for i := 0; i < len(stmt.Proofs[index])-1; i++ {
			curStmt := stmt.Proofs[index][i]
			ret := exec.Stmt(curStmt)
			if ret.IsNotTrue() {
				return ret
			}
		}

		lastStmt := stmt.Proofs[index][len(stmt.Proofs[index])-1]

		if impossibleStmt, ok := lastStmt.(*ast.ImpossibleStmt); ok {
			ret := exec.Stmt(impossibleStmt.Fact)
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
			ret := exec.Stmt(lastStmt)
			if ret.IsNotTrue() {
				return ret
			}
		}

		for _, thenFact := range stmt.ThenFacts {
			ret := exec.Stmt(thenFact)
			if ret.IsNotTrue() {
				return ret
			}
		}
	}

	return ast.NewTrueStmtEmptyRet(stmt)
}
