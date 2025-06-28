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

		execState, err := exec.importDirWithPkgName(stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		execSuccess = execState == glob.ExecState_True
		return execState, nil
	}
}

// Recursively 地找到所有的包和子包的main文件，把里面的东西都提取出来到全局里
func (exec *Executor) importDirWithPkgName(stmt *ast.ImportStmt) (glob.ExecState, error) {
	glob.TaskDirName = filepath.Join(glob.TaskDirName, stmt.Path)
	mainFilePath := filepath.Join(glob.TaskDirName, "main.lix")

	code, err := os.ReadFile(mainFilePath)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// TODO 这里有问题，即使我不运行，我也应该能把stmt传出去
	var execState glob.ExecState = glob.ExecState_True
	topStmtSlice, err := getGloballyImportedStmtSlice(string(code))
	if err != nil {
		return glob.ExecState_Error, err
	}

	if !glob.AssumeImportFilesAreTrue {
		execState, err = exec.runSourceCode(true, string(code), stmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Error, fmt.Errorf("failed to execute import statement")
		}
	}

	execState, err = exec.runGloballyImportedStmts(topStmtSlice)
	if err != nil {
		return glob.ExecState_Error, err
	}

	return execState, nil
}

func (exec *Executor) runSourceCode(runInNewEnv bool, sourceCode string, importStmt *ast.ImportStmt) (glob.ExecState, error) {
	if runInNewEnv {
		exec.newEnv(exec.env, nil)
		defer func() {
			exec.deleteEnvAndRetainMsg()
		}()
	}

	topStmtSlice, err := parser.ParseSourceCode(sourceCode)
	var execState glob.ExecState = glob.ExecState_True
	if err != nil {
		return glob.ExecState_Error, err
	}
	for _, topStmt := range topStmtSlice {
		execState, err = exec.Stmt(topStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Error, fmt.Errorf("failed to execute source code when executing '%s':\n%s", importStmt.String(), topStmt.String())
		}
	}

	return execState, nil
}

func (exec *Executor) runGloballyImportedStmts(topStmtSlice []ast.Stmt) (glob.ExecState, error) {
	upMostEnv := exec.env.GetUpMostEnv()
	newExec := NewExecutor(upMostEnv)

	for _, topStmt := range topStmtSlice {
		execState, err := newExec.assumeStmtIsTrueRun(topStmt)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return glob.ExecState_Error, fmt.Errorf("failed to execute source code:\n%s\nSome statements in the source code are not executed successfully", topStmt.String())
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
	execState, err := exec.runSourceCode(false, string(code), stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
	}

	return glob.ExecState_True, nil
}

func getGloballyImportedStmtSlice(code string) ([]ast.Stmt, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}

	ret := []ast.Stmt{}
	for _, topStmt := range topStmtSlice {
		if topStmtAsImportGlobally, ok := topStmt.(*ast.ImportGloballyStmt); ok {
			codeInside, err := os.ReadFile(filepath.Join(glob.TaskDirName, topStmtAsImportGlobally.Path))
			if err != nil {
				return nil, err
			}
			stmtInside, err := parser.ParseSourceCode(string(codeInside))
			if err != nil {
				return nil, err
			}
			ret = append(ret, stmtInside...)
		} else if _, ok := topStmt.(*ast.ImportStmt); ok {
			continue
		} else {
			ret = append(ret, topStmt)
		}
	}

	return ret, nil
}
