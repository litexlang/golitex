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

func (exec *Executor) proveInRangeStmtWhenParamIsIndex(stmt *ast.ProveInRangeStmt2, i int64) ExecRet {
	indexAsFc := ast.Atom(fmt.Sprintf("%d", i))
	param := stmt.Param()
	uniMap := map[string]ast.Obj{param: indexAsFc}
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	defObjStmt := ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordInteger)}, []ast.FactStmt{ast.NewEqualFact(ast.Atom(param), indexAsFc)}, stmt.GetLine())
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Check dom facts
	for _, domFact := range stmt.GetDomFactsOrNil() {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}
		execState := exec.factStmt(instDomFact)
		if execState.IsErr() {
			return execState
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specFact, ok := domFact.(*ast.SpecFactStmt)
			if !ok {
				return NewExecErr(fmt.Sprintf("dom fact in prove_in_range must be a SpecFactStmt to reverse: %s", domFact.String()))
			}
			revInstDomFact := specFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.InstantiateFact(uniMap)
				if err != nil {
					return NewExecErr(err.Error())
				}
				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return NewExecErr(fmt.Sprintf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			}

			return NewEmptyExecTrue()
		}

		ret := exec.Env.NewFact(domFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// exec proofs
	for _, curStmt := range stmt.GetProofsOrNil() {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState
		}
		if execState.IsUnknown() {
			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
			curStmtAsFact, ok := curStmt.(ast.FactStmt)
			if ok {
				instFact, err := curStmtAsFact.InstantiateFact(uniMap)
				if err != nil {
					return NewExecErr(err.Error())
				}

				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return NewExecErr(fmt.Sprintf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			} else {
				return NewExecErr(fmt.Sprintf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", curStmt.String()))
			}
		}
	}

	// 满足 then
	for _, thenFact := range stmt.GetThenFacts() {
		instThenFact, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}

		execState = exec.factStmt(instThenFact)
		if execState.IsErr() {
			return execState
		}
		if execState.IsUnknown() {
			return NewExecErr(fmt.Sprintf("then fact in prove_in_range must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
		}
	}

	return NewEmptyExecTrue()
}
