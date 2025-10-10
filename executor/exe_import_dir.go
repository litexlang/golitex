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
	parser "golitex/parser"
	"os"
	"path/filepath"
)

func (exec *Executor) importDirStmt(stmt *ast.ImportDirStmt) (glob.ExecState, error) {
	panic("TODO: not implemented")
}

func (exec *Executor) importDirStmt2(stmt *ast.ImportDirStmt) (glob.ExecState, error) {
	exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("start importing directory \"%s\"\n", stmt.Path))

	if !glob.AllowImport {
		return glob.ExecStateError, fmt.Errorf("imported file should not contain import statement, get %s", stmt)
	}

	// err := glob.ImportDirStmtInit(stmt.AsPkgName, stmt.Path)
	// if err != nil {
	// 	return glob.ExecStateError, err
	// }

	execSuccess := false
	defer func() {
		// glob.ImportDirStmtEnd()
		if !execSuccess {
			if glob.RequireMsg() {
				exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("Failed to execute import statement:\n%s\n", stmt))
			}
		} else {
			if glob.RequireMsg() {
				exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("import directory \"%s\" success\n", stmt.Path))
			}
		}
	}()

	execState, err := exec.importDirWithPkgName(stmt)
	if err != nil {
		return glob.ExecStateError, err
	}
	execSuccess = execState == glob.ExecStateTrue

	return execState, nil
}

// Recursively 地找到所有的包和子包的main文件，把里面的东西都提取出来到全局里
func (exec *Executor) importDirWithPkgName(stmt *ast.ImportDirStmt) (glob.ExecState, error) {
	// glob.TaskDirName = filepath.Join(glob.TaskDirName, stmt.Path)
	mainFilePath := filepath.Join(glob.CurrentTaskDirName, glob.PkgEntranceFileName)

	code, err := os.ReadFile(mainFilePath)
	if err != nil {
		return glob.ExecStateError, err
	}

	// TODO 这里有问题，即使我不运行，我也应该能把stmt传出去
	var execState glob.ExecState = glob.ExecStateTrue
	topStmtSlice, err := getGloballyImportedStmtSlice(string(code))
	if err != nil {
		return glob.ExecStateError, err
	}

	if !glob.AssumeImportFilesAreTrue {
		execState, err = exec.runSourceCode(true, string(code), stmt)
		if err != nil {
			return glob.ExecStateError, err
		}
		if execState != glob.ExecStateTrue {
			return glob.ExecStateError, fmt.Errorf("failed to execute import statement")
		}
	}

	execState, err = exec.runStmtInUpmostEnv_AssumeTheyAreTrue(topStmtSlice)
	if err != nil {
		return glob.ExecStateError, err
	}

	return execState, nil
}

func (exec *Executor) runSourceCode(runInNewEnv bool, sourceCode string, importStmt ast.ImportStmtInterface) (glob.ExecState, error) {
	if runInNewEnv {
		exec.NewEnv(exec.env)
		defer func() {
			exec.deleteEnvAndRetainMsg()
		}()
	}

	topStmtSlice, err := parser.ParseSourceCode(sourceCode)
	var execState glob.ExecState = glob.ExecStateTrue
	if err != nil {
		return glob.ExecStateError, err
	}
	for _, topStmt := range topStmtSlice {
		execState, _, err = exec.Stmt(topStmt)
		if err != nil {
			return glob.ExecStateError, err
		}
		if execState != glob.ExecStateTrue {
			return glob.ExecStateError, fmt.Errorf("failed to execute source code when executing '%s':\n%s", importStmt, topStmt)
		}
	}

	return execState, nil
}

func (exec *Executor) runStmtInUpmostEnv_AssumeTheyAreTrue(topStmtSlice []ast.Stmt) (glob.ExecState, error) {
	curEnv := exec.env.GetUpMostEnv()
	newExec := NewExecutor(curEnv)

	for _, topStmt := range topStmtSlice {
		// execState, err := newExec.assumeStmtIsTrueRun(topStmt)
		execState, _, err := newExec.Stmt(topStmt)
		if err != nil {
			return glob.ExecStateError, err
		}
		if execState != glob.ExecStateTrue {
			return glob.ExecStateError, fmt.Errorf("failed to execute source code:\n%s\nSome statements in the source code are not executed successfully", topStmt)
		}
	}
	return glob.ExecStateTrue, nil
}

func getGloballyImportedStmtSlice(code string) ([]ast.Stmt, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}

	ret := []ast.Stmt{}
	for _, topStmt := range topStmtSlice {
		if _, ok := topStmt.(*ast.ImportDirStmt); ok {
			continue
		} else {
			ret = append(ret, topStmt)
		}
	}

	return ret, nil
}
