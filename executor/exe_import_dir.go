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
	parser "golitex/parser"
)

func (exec *Executor) importDirStmt(stmt *ast.ImportDirStmt) (ExecRet, error) {
	panic("TODO: not implemented")
}

func (exec *Executor) runSourceCode(runInNewEnv bool, sourceCode string, importStmt ast.ImportStmtInterface) (ExecRet, error) {
	if runInNewEnv {
		exec.NewEnv(exec.env)
		defer func() {
			exec.deleteEnvAndRetainMsg()
		}()
	}

	topStmtSlice, err := parser.ParseSourceCode(sourceCode)
	var execState ExecRet = NewExecTrue("")
	if err != nil {
		return NewExecErr(""), err
	}
	for _, topStmt := range topStmtSlice {
		execState, _, err = exec.Stmt(topStmt)
		if err != nil {
			return NewExecErr(""), err
		}
		if execState.IsUnknown() {
			return NewExecErr(""), fmt.Errorf("failed to execute source code when executing '%s':\n%s", importStmt, topStmt)
		}
	}

	return execState, nil
}

func (exec *Executor) runStmtInUpmostEnv_AssumeTheyAreTrue(topStmtSlice []ast.Stmt) (ExecRet, error) {
	curEnv := exec.env.GetUpMostEnv()
	newExec := NewExecutor(curEnv)

	for _, topStmt := range topStmtSlice {
		// execState, err := newExec.assumeStmtIsTrueRun(topStmt)
		execState, _, err := newExec.Stmt(topStmt)
		if err != nil {
			return NewExecErr(""), err
		}
		if execState.IsUnknown() {
			return NewExecErr(""), fmt.Errorf("failed to execute source code:\n%s\nSome statements in the source code are not executed successfully", topStmt)
		}
	}
	return NewExecTrue(""), nil
}
