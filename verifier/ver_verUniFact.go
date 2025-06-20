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
// Litex Zulip community: https://litex.zulipchat.com

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
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()

	// 声明变量
	paramMap, paramMapStrToStr, indexes := processUniFactParams(ver.env, oldStmt.Params)

	// 这里要复制一份，因为oldStmt是传入的，不能修改
	var err error
	var newStmtPtr *ast.UniFactStmt = oldStmt

	if len(paramMap) == 0 {
		err := ver.env.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt(oldStmt.Params, oldStmt.ParamSets, []ast.FactStmt{}))
		if err != nil {
			return false, err
		}
	} else {
		newStmtPtr, err = ast.InstantiateUniFact(oldStmt, paramMap)
		if err != nil {
			return false, err
		}

		for i, param := range oldStmt.Params {
			if newParam, ok := paramMapStrToStr[param]; ok {
				newStmtPtr.Params[i] = newParam
			}
		}

		for i, indexStr := range indexes {
			err := ver.env.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt([]string{indexStr}, []ast.Fc{newStmtPtr.ParamSets[i]}, []ast.FactStmt{}))
			if err != nil {
				return false, err
			}
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

	if newStmtPtr.IffFacts == nil || len(newStmtPtr.IffFacts) == 0 {
		return ver.uniFactWithoutIff(newStmtPtr, state)
	} else {
		return ver.uniFactWithIff(newStmtPtr, state)
	}
}

func (ver *Verifier) uniFactWithoutIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) uniFactWithIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ok, err := ver.uniFactWithIff_CheckThenToIff(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.uniFactWithIff_CheckIffToThen(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIff_CheckThenToIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.ThenFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.IffFacts {
		ok, err := ver.VerFactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.newMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFact(toCheckFact)
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

func (ver *Verifier) uniFactWithIff_CheckIffToThen(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.IffFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.ThenFacts {
		ok, err := ver.VerFactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.newMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFact(toCheckFact)
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

func processUniFactParams(env *env.Env, params []string) (map[string]ast.Fc, map[string]string, map[int]string) {
	paramMap := make(map[string]ast.Fc)
	paramMapStrToStr := make(map[string]string)
	indexes := make(map[int]string)
	for i, param := range params {
		newParam := param
		if env.IsAtomDeclared(ast.NewFcAtom(glob.EmptyPkg, newParam), map[string]struct{}{}) {
			newParam = generateUndeclaredRandomName(env)
		}
		if param != newParam {
			paramMap[param] = ast.NewFcAtom(glob.EmptyPkg, newParam)
			paramMapStrToStr[param] = newParam
			indexes[i] = newParam
		}
	}
	return paramMap, paramMapStrToStr, indexes
}

func generateUndeclaredRandomName(env *env.Env) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		if !env.IsAtomDeclared(ast.NewFcAtom(glob.EmptyPkg, randomStr), map[string]struct{}{}) {
			return randomStr
		}
		i++
	}
}
