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
)

func (exec *Executor) proveByInductionStmt(stmt *ast.ProveByInductionStmt) (glob.ExecState, error) {
	var err error
	ver := verifier.NewVerifier(exec.env)
	isOk := false
	msg := ""

	defer func() {
		if glob.RequireMsg() {
			if err != nil {
				exec.newMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
				exec.newMsg(err.Error())
			} else if !isOk {
				exec.newMsg(fmt.Sprintf("%s\nfailed\n", stmt.String()))
				if msg != "" {
					exec.newMsg(msg)
				}
			} else {
				exec.newMsg(fmt.Sprintf("%s\nsuccess\n", stmt.String()))
			}
		}
	}()

	// 输入的 Start 必须是 N_pos
	startIsNPos := exec.proveByInduction_Fact_Start_is_NPos(stmt)
	ok, err := ver.VerFactStmt(startIsNPos, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		msg = fmt.Sprintf("%s\nis unknown", startIsNPos.String())
		return glob.ExecState_Unknown, nil
	}

	// 把start代入fact，得到的fact是true
	startFact, err := exec.proveByInduction_newStartFact(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	ok, err = ver.VerFactStmt(startFact, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		msg = fmt.Sprintf("%s\nis unknown", startFact.String())
		return glob.ExecState_Unknown, nil
	}

	// 对于任意n对于fact成立，那么对于n+1也成立
	uniFact_n_true_leads_n_plus_1_true, err := exec.proveByInduction_newUniFact_n_true_leads_n_plus_1_true(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	ok, err = ver.VerFactStmt(uniFact_n_true_leads_n_plus_1_true, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if !ok {
		msg = fmt.Sprintf("%s\nis unknown", uniFact_n_true_leads_n_plus_1_true.String())
		return glob.ExecState_Unknown, nil
	}

	isOk = true

	return glob.ExecState_True, nil
}

func (exec *Executor) proveByInduction_Fact_Start_is_NPos(stmt *ast.ProveByInductionStmt) *ast.SpecFactStmt {
	startIsNPos := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.Start, ast.FcAtom(glob.KeywordNPos)})
	return startIsNPos
}

func (exec *Executor) proveByInduction_newStartFact(stmt *ast.ProveByInductionStmt) (ast.FactStmt, error) {
	startFact, err := stmt.Fact.Instantiate(map[string]ast.Fc{stmt.Param: stmt.Start})
	return startFact, err
}

func (exec *Executor) proveByInduction_newUniFact_n_true_leads_n_plus_1_true(stmt *ast.ProveByInductionStmt) (ast.FactStmt, error) {
	uniMap := map[string]ast.Fc{stmt.Param: ast.NewFcFn(ast.FcAtom(glob.KeySymbolPlus), []ast.Fc{ast.FcAtom(stmt.Param), ast.FcAtom("1")})}

	retUniFactDom := []ast.FactStmt{
		ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLargerEqual), []ast.Fc{ast.FcAtom(stmt.Param), stmt.Start}),
		stmt.Fact,
	}

	retUniFactThen, err := stmt.Fact.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	return ast.NewUniFact([]string{stmt.Param}, []ast.Fc{ast.FcAtom(glob.KeywordNPos)}, retUniFactDom, []ast.FactStmt{retUniFactThen}), nil
}
