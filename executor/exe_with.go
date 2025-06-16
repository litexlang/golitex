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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) withStmt(stmt *ast.WithStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	state, err := exec.withStmt_checkFact(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if state != glob.ExecState_True {
		return state, nil
	}

	state, err = exec.withStmt_storeFactsToParentEnv(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if state != glob.ExecState_True {
		return state, nil
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) withStmt_checkFact(stmt *ast.WithStmt) (glob.ExecState, error) {
	// exec.newEnv(exec.env, exec.env.CurMatchEnv)
	exec.newEnv(exec.env, &stmt.Fact)
	defer exec.deleteEnvAndRetainMsg()

	// check fact
	execState, err := exec.factStmt(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		exec.appendWarningMsg("with fact is not true:\n%s", stmt.Fact.String())
		return execState, nil
	}

	// run stmt body
	for _, bodyFact := range stmt.Body {
		execState, err = exec.stmt(bodyFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		if execState != glob.ExecState_True {
			return execState, nil
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) withStmt_storeFactsToParentEnv(stmt *ast.WithStmt) (glob.ExecState, error) {
	execState, err := exec.storeFactsInWithStmt(stmt)
	if err != nil {
		return glob.ExecState_Error, err
	}
	if execState != glob.ExecState_True {
		return execState, nil
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) storeFactsInWithStmt(stmt *ast.WithStmt) (glob.ExecState, error) {
	exec.env.CurMatchProp = &stmt.Fact
	defer func() {
		exec.env.CurMatchProp = nil
	}()

	insideFacts := []ast.FactStmt{}
	for _, fact := range stmt.Body {
		if asFact, ok := fact.(ast.FactStmt); ok {
			insideFacts = append(insideFacts, asFact)
		}
	}

	for _, fact := range insideFacts {
		ok := exec.env.AtomsInFactAreDeclared(fact)
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("fact %s has undeclared atoms", fact.String())
		}
		err := exec.env.NewFact(fact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	return glob.ExecState_True, nil
}
