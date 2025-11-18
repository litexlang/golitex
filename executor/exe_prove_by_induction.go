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

func (exec *Executor) proveByInductionStmt(stmt *ast.ProveByInductionStmt) ExecRet {
	var err error
	ver := NewVerifier(exec.Env)
	msg := ""

	// 输入的 Start 必须是 N_pos
	startIsNPos := proveByInduction_Fact_Start_is_NPos(stmt)
	verRet := ver.VerFactStmt(startIsNPos, Round0NoMsg)
	if verRet.IsErr() {
		var result ExecRet = NewExecErr(fmt.Errorf(verRet.String()).Error())
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(verRet.String())
		return result
	}
	if verRet.IsUnknown() {
		msg = fmt.Sprintf("%s\nis unknown", startIsNPos.String())
		var result ExecRet = NewExecUnknown("")
		result = result.AddMsg(fmt.Sprintf("%s\nfailed\n", stmt.String()))
		if msg != "" {
			result = result.AddMsg(msg)
		}
		return result
	}

	// 把start代入fact，得到的fact是true
	startFact, err := proveByInduction_newStartFact(stmt)
	if err != nil {
		var result ExecRet = NewExecErr(err.Error())
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(err.Error())
		return result
	}
	verRet = ver.VerFactStmt(startFact, Round0NoMsg)
	if verRet.IsErr() {
		result := verRet
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(verRet.String())
		return result
	}
	if verRet.IsUnknown() {
		msg = fmt.Sprintf("%s\nis unknown", startFact.String())
		var result ExecRet = NewExecUnknown("")
		result = result.AddMsg(fmt.Sprintf("%s\nfailed\n", stmt.String()))
		if msg != "" {
			result = result.AddMsg(msg)
		}
		return result
	}

	// 对于任意n对于fact成立，那么对于n+1也成立
	uniFact_n_true_leads_n_plus_1_true, err := proveByInduction_newUniFact_n_true_leads_n_plus_1_true(stmt)
	if err != nil {
		var result ExecRet = NewExecErr(err.Error())
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(err.Error())
		return result
	}
	verRet = ver.VerFactStmt(uniFact_n_true_leads_n_plus_1_true, Round0NoMsg)
	if verRet.IsErr() {
		var result ExecRet = NewExecErr(fmt.Errorf(verRet.String()).Error())
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(verRet.String())
		return result
	}
	if verRet.IsUnknown() {
		msg = fmt.Sprintf("%s\nis unknown", uniFact_n_true_leads_n_plus_1_true.String())
		var result ExecRet = NewExecUnknown("")
		result = result.AddMsg(fmt.Sprintf("%s\nfailed\n", stmt.String()))
		if msg != "" {
			result = result.AddMsg(msg)
		}
		return result
	}

	// 对于任何 param >= start, fact 成立
	uniFact_forall_param_geq_start_then_fact_is_true := proveByInduction_newUniFact_forall_param_geq_start_then_fact_is_true(stmt)
	err = exec.Env.NewFact(uniFact_forall_param_geq_start_then_fact_is_true)
	if err != nil {
		var result ExecRet = NewExecErr(err.Error())
		result = result.AddMsg(fmt.Sprintf("%s\nerror\n", stmt.String()))
		result = result.AddMsg(err.Error())
		return result
	}

	var result ExecRet = NewExecTrue("")
	result = result.AddMsg(fmt.Sprintf("%s\nsuccess\n", stmt.String()))
	return result
}

func proveByInduction_Fact_Start_is_NPos(stmt *ast.ProveByInductionStmt) *ast.SpecFactStmt {
	startIsNPos := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeywordIn), []ast.Obj{stmt.Start, ast.AtomObj(glob.KeywordNPos)}, stmt.Line)
	return startIsNPos
}

func proveByInduction_newStartFact(stmt *ast.ProveByInductionStmt) (ast.FactStmt, error) {
	startFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: stmt.Start})
	return startFact, err
}

func proveByInduction_newUniFact_n_true_leads_n_plus_1_true(stmt *ast.ProveByInductionStmt) (ast.FactStmt, error) {
	uniMap := map[string]ast.Obj{stmt.Param: ast.NewFnObj(ast.AtomObj(glob.KeySymbolPlus), []ast.Obj{ast.AtomObj(stmt.Param), ast.AtomObj("1")})}

	retUniFactDom := []ast.FactStmt{
		ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeySymbolLargerEqual), []ast.Obj{ast.AtomObj(stmt.Param), stmt.Start}, stmt.Line),
		stmt.Fact,
	}

	retUniFactThen, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.AtomObj(glob.KeywordNPos)}, retUniFactDom, []ast.FactStmt{retUniFactThen}, stmt.Line), nil
}

func proveByInduction_newUniFact_forall_param_geq_start_then_fact_is_true(stmt *ast.ProveByInductionStmt) ast.FactStmt {
	if asAtom, ok := stmt.Start.(ast.AtomObj); ok && string(asAtom) == "1" {
		return ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.AtomObj(glob.KeywordNPos)}, []ast.FactStmt{}, []ast.FactStmt{stmt.Fact}, stmt.Line)
	}

	return ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.AtomObj(glob.KeywordNPos)}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(glob.KeySymbolLargerEqual), []ast.Obj{ast.AtomObj(stmt.Param), stmt.Start}, stmt.Line)}, []ast.FactStmt{stmt.Fact}, stmt.Line)
}
