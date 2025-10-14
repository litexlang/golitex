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
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (exec *Executor) proveInRangeStmt(stmt *ast.ProveInRangeStmt) (glob.ExecState, error) {
	startStr := strconv.FormatInt(stmt.Start, 10)
	endStr := strconv.FormatInt(stmt.End, 10)

	forallXInIntensionalSetTheyAreFromStartToEnd := ast.NewUniFact([]string{stmt.Param}, []ast.Fc{stmt.IntensionalSet}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLessEqual), []ast.Fc{ast.FcAtom(startStr), ast.FcAtom(stmt.Param)}, stmt.Line), ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLess), []ast.Fc{ast.FcAtom(stmt.Param), ast.FcAtom(endStr)}, stmt.Line)}, stmt.Line)

	state, err := exec.factStmt(forallXInIntensionalSetTheyAreFromStartToEnd)
	if notOkExec(state, err) {
		return state, err
	}

	for i := stmt.Start; i < stmt.End; i++ {
		_, msg, err := exec.proveInRangeStmtWhenParamIsIndex(stmt, i)
		if err != nil {
			if msg != "" {
				exec.newMsg(msg)
			}
			return glob.ExecStateError, err
		}
	}

	uniFact := stmt.UniFact()
	err = exec.env.NewFact(uniFact)
	if err != nil {
		return glob.ExecStateError, err
	}

	return glob.ExecStateTrue, nil
}

func (exec *Executor) proveInRangeStmtWhenParamIsIndex(stmt *ast.ProveInRangeStmt, i int64) (bool, string, error) {
	panic("")
}
