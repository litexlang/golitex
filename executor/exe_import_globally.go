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

func (exec *Executor) importGloballyStmt(stmt *ast.ImportFileStmt) (glob.ExecState, error) {
	exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("start importing file globally \"%s\"\n", stmt.Path))

	if !glob.AllowImport {
		return glob.ExecState_Error, fmt.Errorf("import globally is not allowed in imported file, get %s", stmt.String())
	}

	glob.AllowImport = false
	defer func() {
		glob.AllowImport = true
	}()

	codePath := filepath.Join(glob.CurrentTaskDirName, stmt.Path)
	code, err := os.ReadFile(codePath)
	if err != nil {
		return glob.ExecState_Error, err
	}

	//parse code
	stmts, err := parser.ParseSourceCode(string(code))
	if err != nil {
		return glob.ExecState_Error, err
	}

	for _, stmt := range stmts {
		execState, err := exec.Stmt(stmt)
		if notOkExec(execState, err) {
			return execState, err
		}
	}

	// 检查是否是顶层，这是必要的，因为有可能 import_globally 就是在最顶层运行的
	if exec.env.Parent != nil {
		return exec.runStmtInUpmostEnv_AssumeTheyAreTrue(stmts)
	}

	exec.env.Msgs = append(exec.env.Msgs, fmt.Sprintf("import file globally \"%s\" success\n", stmt.Path))

	return glob.ExecState_True, nil
}
