// Copyright Jiachen Shen.
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

func SuccessExecStmtStr(stmt ast.Stmt) string {
	return fmt.Sprintf("Success! line %d\n", stmt.GetLine())
}

func UnknownExecStmtStr(stmt ast.Stmt) string {
	return fmt.Sprintf("Unknown: line %d\n", stmt.GetLine())
}

func ErrorExecStmtStr(stmt ast.Stmt) string {
	return fmt.Sprintf("Error: line %d\n", stmt.GetLine())
}

func (exec *Executor) AddStmtToStmtRet(ret *glob.StmtRet, stmt ast.Stmt) *glob.StmtRet {
	ret.SetLine(stmt.GetLine())
	ret.AddStmt(stmt.String())
	return ret
}

func (exec *Executor) NewTrueStmtRetWithStmt(stmt ast.Stmt) *glob.StmtRet {
	ret := glob.NewEmptyStmtTrue()
	exec.AddStmtToStmtRet(ret, stmt)
	return ret
}
