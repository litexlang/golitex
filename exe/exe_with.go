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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) withPropMatchStmt(stmt *ast.WithPropMatchStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	state, err := exec.withPropMatchStmt_checkFact(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if state != glob.ExecState_True {
		return state, nil
	}

	state, err = exec.withPropMatchStmt_storeFactsToParentEnv(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if state != glob.ExecState_True {
		return state, nil
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) withPropMatchStmt_checkFact(stmt *ast.WithPropMatchStmt) (glob.ExecState, error) {
	// exec.newEnv(exec.env, exec.env.CurMatchEnv)
	exec.newEnv(exec.env, &stmt.Fact)
	defer exec.deleteEnvAndRetainMsg()

	// check fact
	execState, err := exec.factStmt(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		exec.appendWarningMsg("with fact is not true:\n%s", stmt.Fact.String())
		return execState, nil
	}

	// run stmt body
	for _, bodyFact := range stmt.Body {
		execState, err = exec.stmt(bodyFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	return glob.ExecState_True, nil
}

// TODO 存
func (exec *Executor) withPropMatchStmt_storeFactsToParentEnv(stmt *ast.WithPropMatchStmt) (glob.ExecState, error) {
	knowSupposeStmt := ast.NewKnowSupposeStmt(*ast.NewSupposeStmt(stmt.Fact, stmt.Body))
	execState, err := exec.knowSupposeStmt(knowSupposeStmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return execState, nil
	}

	return glob.ExecState_True, nil
}
