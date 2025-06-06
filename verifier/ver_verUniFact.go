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
	paramMap, paramMapStrToStr := processUniFactParams(ver.env, oldStmt.Params)

	var newStmt *ast.UniFactStmt = oldStmt
	var err error
	if len(paramMap) == 0 {
		ver.env.ObjDefMem.Insert(ast.NewDefObjStmt(oldStmt.Params, oldStmt.ParamSets, []ast.FactStmt{}), glob.EmptyPkg)
	} else {
		for i, param := range oldStmt.Params {
			if newParam, ok := paramMapStrToStr[param]; ok {
				newStmt.Params[i] = newParam
			}
		}

		newStmt, err = ast.InstantiateUniFact(oldStmt, paramMap)
		if err != nil {
			return false, err
		}
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmt.ParamSets {
		atoms := ast.GetAtomsInFc(paramSet)
		for _, atom := range atoms {
			if !ver.env.IsAtomDeclared(atom) {
				return false, fmt.Errorf("%s is not declared", atom.String())
			}
		}
	}

	// know cond facts
	for _, condFact := range newStmt.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	if newStmt.IffFacts == nil {
		return ver.uniFactWithoutIff(newStmt, state)
	} else {
		return ver.uniFactWithIff(newStmt, state)
	}
}

func (ver *Verifier) uniFactWithoutIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
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
		ok, err := ver.FactStmt(toCheckFact, state)
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
		ok, err := ver.FactStmt(toCheckFact, state)
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

func processUniFactParams(env *env.Env, params []string) (map[string]ast.Fc, map[string]string) {
	paramMap := make(map[string]ast.Fc)
	paramMapStrToStr := make(map[string]string)
	for _, param := range params {
		newParam := param
		for env.IsAtomDeclared(ast.NewFcAtom(glob.EmptyPkg, newParam)) {
			newParam = fmt.Sprintf("%s%s", glob.UniPrefix, newParam)
		}
		if param != newParam {
			paramMap[param] = ast.NewFcAtom(glob.EmptyPkg, newParam)
			paramMapStrToStr[param] = newParam
		}
	}
	return paramMap, paramMapStrToStr
}
