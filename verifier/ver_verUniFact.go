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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verUniFact(oldStmt *ast.UniFactStmt, state VerState) (bool, error) {
	if state.isFinalRound() {
		return false, nil
	}

	// 在局部环境声明新变量
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	// 声明变量
	paramMap, paramMapStrToStr, _ := processUniFactParamsDuplicateDeclared(ver.env, oldStmt.Params)

	var newStmtPtr *ast.UniFactStmt = oldStmt

	if len(paramMap) == 0 {
		err := ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt(oldStmt.Params, oldStmt.ParamSets, []ast.FactStmt{}))
		if err != nil {
			return false, err
		}
	} else {
		instantiatedOldStmt, err := ast.InstantiateUniFact(oldStmt, paramMap)
		if err != nil {
			return false, err
		}

		newParams := []string{}
		for _, param := range oldStmt.Params {
			if newParam, ok := paramMapStrToStr[param]; ok {
				newParams = append(newParams, newParam)
			} else {
				newParams = append(newParams, param)
			}
		}

		newStmtPtr = ast.NewUniFact(newParams, instantiatedOldStmt.ParamSets, instantiatedOldStmt.DomFacts, instantiatedOldStmt.ThenFacts)

		err = ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt(newStmtPtr.Params, newStmtPtr.ParamSets, []ast.FactStmt{}))
		if err != nil {
			return false, err
		}
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmtPtr.ParamSets {
		ok := ver.env.AreAtomsInFcAreDeclared(paramSet, map[string]struct{}{})
		if !ok {
			return false, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(paramSet))
		}
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	return ver.uniFact_checkThenFacts(newStmtPtr, state)
}

func (ver *Verifier) uniFact_checkThenFacts(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.VerFactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.newMsgEnd("%s is unknown", thenFact.String())
			}
			return false, nil
		}

		// if true, store it
		err = ver.env.NewFact(thenFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

func processUniFactParamsDuplicateDeclared(env *env.Env, params []string) (map[string]ast.Fc, map[string]string, map[int]string) {
	paramMap := make(map[string]ast.Fc)
	paramMapStrToStr := make(map[string]string)
	indexesOfDuplicateParams := make(map[int]string)
	for i, param := range params {
		newParam := param
		if env.IsAtomDeclared(ast.FcAtom(newParam), map[string]struct{}{}) {
			newParam = generateUndeclaredRandomName(env)
			paramMap[param] = ast.FcAtom(newParam)
			paramMapStrToStr[param] = newParam
			indexesOfDuplicateParams[i] = newParam
		}
	}
	return paramMap, paramMapStrToStr, indexesOfDuplicateParams
}

func generateUndeclaredRandomName(env *env.Env) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		// if !env.IsAtomDeclared(ast.NewFcAtom(glob.EmptyPkg, randomStr), map[string]struct{}{}) {
		if !env.IsAtomDeclared(ast.FcAtom(randomStr), map[string]struct{}{}) {
			return randomStr
		}
		i++
	}
}
