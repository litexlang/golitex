// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_executor

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	verifier "golitex/litex_verifier"
)

func (exec *Executor) factStmt(stmt ast.FactStmt) (glob.ExecState, error) {
	defer exec.appendNewMsg("\n")

	ok, _, err := exec.checkFactStmt(stmt)

	if err != nil {
		return glob.ExecState_Error, err
	}

	if ok {
		return glob.ExecState_True, exec.env.NewFact(stmt)
	}

	if glob.CheckFalse {
		switch stmt := stmt.(type) {
		case *ast.SpecFactStmt:
			newStmt := stmt.ReverseIsTrue()
			ok, _, err := exec.checkFactStmt(newStmt)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if ok {
				exec.appendNewMsg(stmt.String() + "\nis false")
				return glob.ExecState_False, nil
			}
		case *ast.ConUniFactStmt:
			// TODO 这里需要考虑到fact的类型
		default:
			// TODO 这里需要考虑到fact的类型
		}
		exec.appendNewMsg(stmt.String() + "\nis unknown")
	}

	exec.appendNewMsg(stmt.String() + "\nis unknown")

	return glob.ExecState_Unknown, nil
}

func (exec *Executor) checkFactStmt(stmt ast.FactStmt) (bool, *verifier.Verifier, error) {
	curVerifier := verifier.NewVerifier(exec.env, exec.env.CurPkg)
	ok, err := curVerifier.FactStmt(stmt, verifier.Round0Msg)
	if err != nil {
		return false, curVerifier, err
	}
	return ok, curVerifier, err
}
