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

		execState, unknownStmt, err := exec.proveInRangeStmtDeclareParamExecProofs(stmt, i)
		if err != nil {
			return glob.ExecStateError, err
		}
		if execState != glob.ExecStateTrue {
			return execState, fmt.Errorf("when %s = %d, %s\nis unknown", stmt.Param, i, unknownStmt.String())
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
			revInstDomFact := domFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.Instantiate(uniMap)
				if err != nil {
					return false, err
				}
				ok, err := ver.VerFactStmt(instFact, verifier.Round0NoMsg)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, fmt.Errorf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String())
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

func (exec *Executor) proveInRangeStmtDeclareParamExecProofs(stmt *ast.ProveInRangeStmt, i int64) (glob.ExecState, ast.Stmt, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndGiveUpMsgs()

	defObjKnownFacts := make([]ast.FactStmt, len(stmt.DomFacts))
	for i, domFact := range stmt.DomFacts {
		defObjKnownFacts[i] = domFact
	}

	defObjStmt := ast.NewDefObjStmt([]string{stmt.Param}, []ast.Fc{ast.FcAtom(glob.KeywordInteger)}, defObjKnownFacts, stmt.Line)
	err := exec.defObjStmt(defObjStmt)
	if err != nil {
		return glob.ExecStateError, nil, err
	}

	// exec proofs
	for _, curStmt := range stmt.Proofs {
		execState, _, err := exec.Stmt(curStmt)
		if err != nil {
			return glob.ExecStateError, nil, err
		}
		if execState != glob.ExecStateTrue {
			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
			uniMap := map[string]ast.Fc{stmt.Param: ast.FcAtom(fmt.Sprintf("%d", i))}
			curStmtAsFact, err := curStmt.(ast.FactStmt).Instantiate(uniMap)
			if err != nil {
				return glob.ExecStateError, nil, err
			}

			execState, err := exec.factStmt(curStmtAsFact)
			if err != nil {
				return glob.ExecStateError, nil, err
			}
			if execState != glob.ExecStateTrue {
				return glob.ExecStateUnknown, curStmt, fmt.Errorf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", curStmtAsFact.String())
			}
		}
	}
	return glob.ExecStateTrue, nil, nil
}
