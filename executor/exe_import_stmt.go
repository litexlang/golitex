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
	"os"
	"path/filepath"
	"strings"
)

func (exec *Executor) importStmt(stmt *ast.ImportStmt) (glob.ExecState, error) {
	if stmt.AsPkgName == "" {
		execState, err := exec.importFileWithoutPkgName(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}

		return execState, nil
	} else {
		err := glob.ImportStmtInit(stmt.AsPkgName)
		if err != nil {
			return glob.ExecState_Error, err
		}

		execSuccess := false
		defer func() {
			glob.ImportStmtEnd()
			if !execSuccess {
				if glob.IsNotImportState() {
					exec.appendMsg(fmt.Sprintf("Failed to execute import statement:\n%s\n", stmt.String()))
				}
			} else {
				if glob.IsNotImportState() {
					exec.appendMsg(fmt.Sprintf("%s\n", stmt.String()))
				}
			}
		}()

		if strings.HasSuffix(stmt.Path, ".lix") {
			execState, err := exec.importFileWithPkgName(stmt)
			if err != nil {
				return glob.ExecState_Error, err
			}
			execSuccess = execState == glob.ExecState_True
			return execState, nil
		} else {
			execState, err := exec.importDirWithPkgName(stmt)
			if err != nil {
				return glob.ExecState_Error, err
			}
			execSuccess = execState == glob.ExecState_True
			return execState, nil
		}
	}

}

func (exec *Executor) runFileToMakeSureTheFileIsTrue(codePath string) (glob.ExecState, []*ast.PubStmt, error) {
	code, err := os.ReadFile(codePath)
	if err != nil {
		return glob.ExecState_Error, nil, err
	}

	var execState glob.ExecState = glob.ExecState_True
	var pubStmtSlice []*ast.PubStmt = []*ast.PubStmt{}
	if !glob.AssumeImportFilesAreTrue {
		execState, pubStmtSlice, err = exec.runSourceCode(true, string(code))
		if err != nil {
			return glob.ExecState_Error, nil, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Error, nil, fmt.Errorf("failed to execute import statement")
		}
	}

	return execState, pubStmtSlice, nil
}

func (exec *Executor) runSourceCode(runInNewEnv bool, sourceCode string) (glob.ExecState, []*ast.PubStmt, error) {
	if runInNewEnv {
		exec.newEnv(exec.env, nil)
		defer func() {
			exec.deleteEnvAndRetainMsg()
		}()
	}

	topStmtSlice, err := parser.ParseSourceCode(sourceCode)
	var pubStmtSlice []*ast.PubStmt = []*ast.PubStmt{}
	var execState glob.ExecState = glob.ExecState_True
	if err != nil {
		return glob.ExecState_Error, nil, err
	}
	for _, topStmt := range topStmtSlice {
		execState, err = exec.Stmt(topStmt)
		if err != nil {
			return glob.ExecState_Error, nil, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Error, nil, fmt.Errorf("failed to execute source code:\n%s\nSome statements in the source code are not executed successfully", sourceCode)
		}
		if pubStmt, ok := topStmt.(*ast.PubStmt); ok {
			pubStmtSlice = append(pubStmtSlice, pubStmt)
		}
	}

	return execState, pubStmtSlice, nil
}

func (exec *Executor) runSourceCodePubStmt(pubStmtSlice []*ast.PubStmt) (glob.ExecState, error) {
	upMostEnv := exec.env.GetUpMostEnv()
	newExec := NewExecutor(upMostEnv)

	for _, pubStmt := range pubStmtSlice {
		for _, stmt := range pubStmt.Stmts {
			execState, err := newExec.assumeStmtIsTrueRun(stmt)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if execState != glob.ExecState_True {
				return glob.ExecState_Error, fmt.Errorf("failed to execute source code:\n%s\nSome statements in the source code are not executed successfully", pubStmt.String())
			}
		}
	}
	return glob.ExecState_True, nil
}

func (exec *Executor) importFileWithoutPkgName(stmt *ast.ImportStmt) (glob.ExecState, error) {
	codePath := filepath.Join(glob.TaskDirName, stmt.Path)
	code, err := os.ReadFile(codePath)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// read the file
	execState, _, err := exec.runSourceCode(false, string(code))
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) importFileWithPkgName(stmt *ast.ImportStmt) (glob.ExecState, error) {
	codePath := filepath.Join(glob.TaskDirName, stmt.Path)
	execState, pubStmtSlice, err := exec.runFileToMakeSureTheFileIsTrue(codePath)
	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s", stmt.String())
	}

	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
	}

	execState, err = exec.runSourceCodePubStmt(pubStmtSlice)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return execState, nil
}

func (exec *Executor) importDirWithPkgName(stmt *ast.ImportStmt) (glob.ExecState, error) {
	glob.TaskDirName = filepath.Join(glob.TaskDirName, stmt.Path)

	codePath := filepath.Join(glob.TaskDirName, "main.lix")
	execState, pubStmtSlice, err := exec.runFileToMakeSureTheFileIsTrue(codePath)
	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s", stmt.String())
	}

	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
	}

	execState, err = exec.runSourceCodePubStmt(pubStmtSlice)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return execState, nil
}
