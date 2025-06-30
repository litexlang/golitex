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
	"os"
	"path/filepath"
)

func (exec *Executor) importFileStmt(stmt *ast.ImportFileStmt) (glob.ExecState, error) {
	exec.appendMsg("start importing file \"%s\"\n", stmt.Path)

	if !glob.AllowImport {
		return glob.ExecState_Error, fmt.Errorf("imported file should not contain import statement, get %s", stmt.String())
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

	// read the file
	execState, err := exec.runSourceCode(false, string(code), stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return glob.ExecState_Error, fmt.Errorf("failed to execute import statement:\n%s\nSome statements in the imported file are not executed successfully", stmt.String())
	}

	exec.appendMsg("import file \"%s\" success\n", stmt.Path)

	return glob.ExecState_True, nil
}
