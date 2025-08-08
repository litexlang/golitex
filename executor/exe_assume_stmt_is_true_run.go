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
)

func (exec *Executor) assumeStmtIsTrueRun(stmt ast.Stmt) (glob.ExecState, error) {
	var err error = nil
	var execState glob.ExecState = glob.ExecState_True

	switch stmt := (stmt).(type) {
	case ast.FactStmt:
		knowFact := ast.NewKnowStmt([]ast.CanBeKnownStmt{stmt})
		err = exec.knowStmt(knowFact)
	case *ast.KnowFactStmt:
		err = exec.knowStmt(stmt)
	case *ast.ClaimProveStmt:
		panic("implement me")
	case *ast.DefPropStmt:
		err = exec.defPropStmt(stmt, true)
	case *ast.DefObjStmt:
		err = exec.defObjStmt(stmt, true)
	case *ast.HaveObjStStmt:
		panic("implement me")
	case *ast.DefExistPropStmt:
		err = exec.defExistPropStmt(stmt)
	case *ast.DefFnStmt:
		err = exec.defFnStmt(stmt)
	case *ast.KnowPropStmt:
		err = exec.knowPropStmt(stmt)
	case *ast.ProveInEachCaseStmt:
		panic("implement me")
	case *ast.ImportDirStmt:
		return glob.ExecState_True, nil
	case *ast.ProveStmt:
		panic("implement me")
	case *ast.ClaimProveByContradictionStmt:
		panic("implement me")
	// case *ast.DefFnTemplateStmt:
	// 	err = exec.defFnTemplateStmt(stmt)
	case *ast.ImportFileStmt:
		return glob.ExecState_True, nil
	case *ast.KnowExistPropStmt:
		_, err = exec.knowExistPropStmt(stmt)
	default:
		err = fmt.Errorf("unknown statement type: %T", stmt)
	}

	return execState, err
}
