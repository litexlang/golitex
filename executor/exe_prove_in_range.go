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
	verifier "golitex/verifier"
)

func (exec *Executor) proveInRangeStmt(stmt *ast.ProveInRangeStmt) (glob.ExecState, error) {
	for i := stmt.Start; i <= stmt.End; i++ {
		isT, err := exec.proveInRangeStmtCheckCurNumSatisfyDom(i, stmt)
		if err != nil {
			return glob.ExecStateError, err
		}
		if !isT {
			continue
		}
		execState, unknownStmt, err := exec.execStmts(stmt.Proofs)
		if err != nil {
			return glob.ExecStateError, err
		}
		if execState != glob.ExecStateTrue {
			return execState, fmt.Errorf("when index = %d, %d satisfy dom facts, but %s\nis unknown", i, i, unknownStmt.String())
		}
		return glob.ExecStateTrue, nil
	}

	return glob.ExecStateTrue, nil
}

func (exec *Executor) proveInRangeStmtCheckCurNumSatisfyDom(i int64, stmt *ast.ProveInRangeStmt) (bool, error) {
	indexAsFc := ast.FcAtom(fmt.Sprintf("%d", i))
	uniMap := map[string]ast.Fc{stmt.Param: indexAsFc}
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndGiveUpMsgs()

	ver := verifier.NewVerifier(exec.env)

	for _, domFact := range stmt.DomFacts {
		instDomFact, err := domFact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}
		ok, err := ver.VerFactStmt(instDomFact, verifier.Round0NoMsg)
		if err != nil {
			return false, err
		}

		if !ok {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specOrFact, ok := domFact.(ast.Spec_OrFact)
			if !ok {
				return false, fmt.Errorf("dom facts in prove_in_range must be spec or fact, can not be unknown: %s", domFact.String())
			}

			revInstDomFact := specOrFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				ok, err := ver.VerFactStmt(fact, verifier.Round0NoMsg)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, fmt.Errorf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", fact.String())
				}
			}

			return false, nil
		}
	}

	return true, nil
}

func (exec *Executor) execStmts(stmts []ast.Stmt) (glob.ExecState, ast.Stmt, error) {
	for _, curStmt := range stmts {
		execState, _, err := exec.Stmt(curStmt)
		if notOkExec(execState, err) {
			return execState, curStmt, err
		}
	}
	return glob.ExecStateTrue, nil, nil
}
