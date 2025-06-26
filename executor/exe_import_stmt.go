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
	parser "golitex/parser"
	taskManager "golitex/task_manager"
	"os"
	"path/filepath"
)

func (exec *Executor) importStmt(stmt *ast.ImportStmt) error {
	// import name should be valid
	err := glob.IsValidUseDefinedFcAtom(stmt.AsPkgName)
	if err != nil {
		return err
	}

	if _, ok := taskManager.DeclaredPkgNames[stmt.AsPkgName]; ok {
		return fmt.Errorf("duplicate package name: '%s'", stmt.AsPkgName)
	}

	execSuccess := false
	originalMsgLen := exec.env.MsgLen()
	defer func() {
		exec.env.ClearMsgFromIndex(originalMsgLen)
		if !execSuccess {
			exec.appendMsg(fmt.Sprintf("Failed to execute import statement:\n%s\n", stmt.String()))
		} else {
			exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
		}
	}()

	// 需要连上现在所在的repo的名字
	codePath := filepath.Join(taskManager.TaskRepoName, stmt.Path)
	code, err := os.ReadFile(codePath)
	if err != nil {
		return err
	}

	if stmt.AsPkgName == "" {
		// read the file
		topStmtSlice, err := parser.ParseSourceCode(string(code))
		if err != nil {
			return err
		}
		for _, topStmt := range topStmtSlice {
			execState, err := exec.execOnlyPubStmt(topStmt)
			if err != nil {
				return err
			}
			if execState != glob.ExecState_True {
				return fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
			}
		}
		execSuccess = true
	} else {
		panic(glob.InternalWarningMsg("import with as pkg name is not supported"))
	}

	return nil
}

func (exec *Executor) execOnlyPubStmt(stmt ast.Stmt) (glob.ExecState, error) {
	switch stmt := (stmt).(type) {
	case *ast.PubStmt:
		return exec.pubStmt(stmt)
	default:
		return glob.ExecState_True, nil
	}
}
