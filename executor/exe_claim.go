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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	verifier "golitex/verifier"
	"strings"
)

func (exec *Executor) claimStmtProveByContradiction(stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	isSuccess := false

	exec.newEnv(exec.env)
	if glob.RequireMsg() {
		defer func() {
			exec.newMsg("\n")
			if isSuccess {
				exec.appendNewMsgAtBegin("is true\n")
			} else {
				exec.appendNewMsgAtBegin("is unknown\n")
			}
			exec.appendNewMsgAtBegin(stmt.ClaimProveStmt.String())
			exec.deleteEnvAndRetainMsg()
		}()
	}

	switch asStmt := stmt.ClaimProveStmt.ToCheckFact.(type) {
	case ast.OrStmt_SpecStmt:
		return exec.reversibleFactProveByContradiction(asStmt, stmt)
	case *ast.UniFactStmt:
		return exec.uniFactProveByContradiction(asStmt, stmt)
	default:
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support reversible fact or uni fact")
	}
}

func (exec *Executor) reversibleFactProveByContradiction(specFactStmt ast.OrStmt_SpecStmt, stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	reversedFact := specFactStmt.ReverseIsTrue()

	for _, curFact := range reversedFact {
		err := exec.env.NewFact(&curFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	execState, err := exec.execProofBlockAtCurEnv(stmt.ClaimProveStmt.Proofs)
	if notOkExec(execState, err) {
		return execState, err
	}

	lastStmtAsFact, ok := stmt.ClaimProveStmt.Proofs[len(stmt.ClaimProveStmt.Proofs)-1].(ast.OrStmt_SpecStmt)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("prove by contradiction only support fact")
	}

	reversedLastFact := lastStmtAsFact.ReverseIsTrue()

	reversedLastFactStr := []string{"and:"}
	for _, curFact := range reversedLastFact {
		reversedLastFactStr = append(reversedLastFactStr, curFact.String())
	}
	reversedLastFactStrStr := strings.Join(reversedLastFactStr, "\n\t")

	exec.newMsg(fmt.Sprintf("the reversed last statement of current claim statement is:\n%s\nwe prove it(them)\n", reversedLastFactStrStr))

	for _, curFact := range reversedLastFact {
		execState, err = exec.factStmt(&curFact)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	exec.newMsg(fmt.Sprintf("last statement of current claim statement:\n%s\nis true and false. Prove by contradiction is successful!", lastStmtAsFact))

	return glob.ExecState_True, nil
}

func (exec *Executor) uniFactProveByContradiction(specFactStmt *ast.UniFactStmt, stmt *ast.ClaimProveByContradictionStmt) (glob.ExecState, error) {
	ver := verifier.NewVerifier(exec.env)
	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(specFactStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		err := exec.env.NewFact(condFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// suppose reverse of then facts is true
	panic("not implemented")

	return glob.ExecState_True, nil
}
