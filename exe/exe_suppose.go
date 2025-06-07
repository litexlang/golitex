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
	env "golitex/environment"
	glob "golitex/glob"
)

func (exec *Executor) supposePropMatchStmt(stmt *ast.SupposeStmt) (glob.ExecState, error) {
	defer exec.appendMsg(glob.InternalWarningMsg("Currently, locally declared obj might be emitted into global env. Be careful when you declare anything in suppose stmt.\n"))
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	originalEnv := exec.env
	originalEnv.CurMatchProp = &stmt.Fact // 之所以这么干，是因为要把stmt下面的事实存到originalEnv里，而且要存到 matchEnv 里
	defer func() {
		originalEnv.CurMatchProp = nil
	}()

	exec.newEnv(originalEnv, &stmt.Fact)
	defer exec.deleteEnvAndRetainMsg()

	execState, err := exec.supposeStmt_declaredParams(stmt)
	if err != nil || execState != glob.ExecState_True {
		return execState, err
	}

	// run stmt body
	execState, insideFacts, err := exec.supposeStmt_runStmtBody(stmt)
	if err != nil || execState != glob.ExecState_True {
		return execState, err
	}

	execState, err = exec.supposeStmt_storeFactsToParentEnv(insideFacts, stmt, originalEnv)
	if err != nil || execState != glob.ExecState_True {
		return execState, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) supposeStmt_declaredParams(stmt *ast.SupposeStmt) (glob.ExecState, error) {
	// declare new params in suppose environment
	factSpecDef, ok := exec.env.GetPropDef(stmt.Fact.PropName)
	if !ok {
		return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", stmt.Fact.PropName.String())
	}

	if len(factSpecDef.DefHeader.Params) != len(stmt.Fact.Params) {
		return glob.ExecState_Error, fmt.Errorf("spec fact parameter number not equal to prop def params number. expect %d, but got %d", len(factSpecDef.DefHeader.Params), len(stmt.Fact.Params))
	}

	for _, param := range stmt.Fact.Params {
		asAtom, ok := param.(*ast.FcAtom)
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", param.String())
		}
		if asAtom.PkgName != glob.EmptyPkg {
			return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", param.String())
		}
		err := exec.env.ObjDefMem.Insert(ast.NewDefObjStmt([]string{asAtom.Name}, []ast.Fc{}, []ast.FactStmt{}), glob.EmptyPkg)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range factSpecDef.DefHeader.Params {
		uniMap[param] = stmt.Fact.Params[i]
	}

	instantiatedFactSpecDef, err := factSpecDef.Instantiate(uniMap)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// itself is true
	err = exec.env.NewFact(&stmt.Fact)
	if err != nil {
		return glob.ExecState_Error, err
	}

	// in facts are true
	for _, inFact := range instantiatedFactSpecDef.DefHeader.NewInFacts() {
		err = exec.env.NewFact(inFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// dom is true
	for _, domFact := range instantiatedFactSpecDef.DomFacts {
		err = exec.env.NewFact(domFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	// iff is true
	for _, iffFact := range instantiatedFactSpecDef.IffFacts {
		err = exec.env.NewFact(iffFact)
		if err != nil {
			return glob.ExecState_Error, err
		}
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) supposeStmt_runStmtBody(stmt *ast.SupposeStmt) (glob.ExecState, []ast.FactStmt, error) {
	insideFacts := []ast.FactStmt{}
	for _, bodyFact := range stmt.Body {
		execState, err := exec.stmt(bodyFact)
		if err != nil {
			return glob.ExecState_Error, nil, err
		}
		if execState != glob.ExecState_True {
			return execState, nil, nil
		} else {
			// store fact in original env
			if asFact, ok := bodyFact.(ast.FactStmt); ok {
				insideFacts = append(insideFacts, asFact)
			}
			// store known fact in original env
			if asFact, ok := bodyFact.(*ast.KnowFactStmt); ok {
				insideFacts = append(insideFacts, asFact.Facts...)
			}
		}
	}

	return glob.ExecState_True, insideFacts, nil
}

// TODO：这里其实是有问题的，万一涉及到的变量没声明，那就出错了
func (exec *Executor) supposeStmt_storeFactsToParentEnv(insideFacts []ast.FactStmt, stmt *ast.SupposeStmt, storeToEnv *env.Env) (glob.ExecState, error) {
	messages := []string{}
	for _, fact := range insideFacts {
		err := storeToEnv.NewFact(fact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		messages = append(messages, fact.String())
	}

	exec.appendMsg(ast.SupposeNewFactsMsg(stmt, messages))

	return glob.ExecState_True, nil
}
