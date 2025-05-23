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
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) supposePropMatchStmt(stmt *ast.SupposePropMatchStmt) (glob.ExecState, error) {
	defer exec.appendMsg("\n")
	defer exec.appendMsg(stmt.String())

	originalEnv := exec.env
	originalEnv.CurMatchEnv = stmt // 之所以这么干，是因为要把stmt下面的事实存到originalEnv里，而且要存到 matchEnv 里
	defer func() {
		originalEnv.CurMatchEnv = nil
	}()

	exec.newEnv(originalEnv, stmt)
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

	execState, err = exec.supposeStmt_storeFactsToParentEnv_addPrefixToSupposeFactAndBodyFacts(insideFacts, stmt)
	if err != nil || execState != glob.ExecState_True {
		return execState, err
	}

	return glob.ExecState_True, nil
}

func (exec *Executor) supposeStmt_declaredParams(stmt *ast.SupposePropMatchStmt) (glob.ExecState, error) {
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
		err := exec.env.ObjDefMem.Insert(ast.NewDefObjStmt([]string{asAtom.Name}, []ast.FactStmt{}, []ast.FactStmt{}), glob.EmptyPkg)
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
	for _, inFact := range instantiatedFactSpecDef.DefHeader.ParamInSetsFacts {
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

func (exec *Executor) supposeStmt_runStmtBody(stmt *ast.SupposePropMatchStmt) (glob.ExecState, []ast.FactStmt, error) {
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
		}
	}

	return glob.ExecState_True, insideFacts, nil
}

func (exec *Executor) supposeStmt_storeFactsToParentEnv_addPrefixToSupposeFactAndBodyFacts(insideFacts []ast.FactStmt, stmt *ast.SupposePropMatchStmt) (glob.ExecState, error) {
	// store facts in original env
	uniMap := map[string]ast.Fc{}
	for _, supposePropParam := range stmt.Fact.Params {
		asAtom, ok := supposePropParam.(*ast.FcAtom)
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("spec fact parameter must be atom, but got: %s", supposePropParam.String())
		}
		name := asAtom.Name
		nameWithPrefix := fmt.Sprintf("%s%s", glob.UniParamPrefix, name)
		uniMap[name] = ast.NewFcAtom(glob.EmptyPkg, nameWithPrefix)
	}

	factsWithPrefix := []ast.FactStmt{}
	for _, fact := range insideFacts {
		factWithPrefix, err := fact.Instantiate(uniMap)
		if err != nil {
			return glob.ExecState_Error, err
		}
		factsWithPrefix = append(factsWithPrefix, factWithPrefix)
	}

	newPropFactPtr, err := ast.InstantiateSpecFact(&stmt.Fact, uniMap)
	if err != nil {
		return glob.ExecState_Error, err
	}
	stmt.Fact = *newPropFactPtr

	messages := []string{}
	parentEnv := exec.env.Parent
	for _, fact := range factsWithPrefix {
		err := parentEnv.NewFact(fact)
		if err != nil {
			return glob.ExecState_Error, err
		}
		messages = append(messages, fact.String())
	}

	exec.appendMsg(ast.SupposeNewFactsMsg(stmt, messages))

	return glob.ExecState_True, nil
}
