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

	var newStmt *ast.UniFactStmt = oldStmt
	var err error

	if len(paramMap) == 0 {
		err := ver.env.ExeDefObjStmt(ast.NewDefObjStmt(oldStmt.Params, oldStmt.ParamSets, []ast.FactStmt{}))
		if err != nil {
			return false, err
		}
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

		for i, indexStr := range indexes {
			err := ver.env.ExeDefObjStmt(ast.NewDefObjStmt([]string{indexStr}, []ast.Fc{newStmt.ParamSets[i]}, []ast.FactStmt{}))
			if err != nil {
				return false, err
			}
		}
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmt.ParamSets {
		atoms := ast.GetAtomsInFc(paramSet)
		ok := ver.env.AreAtomsDeclared(atoms)
		if !ok {
			return false, fmt.Errorf("atoms %s are not declared", atoms[0].String())
		}
	}

	// know cond facts
	for _, condFact := range newStmt.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	if newStmt.IffFacts == nil || len(newStmt.IffFacts) == 0 {
		return ver.uniFactWithoutIff(newStmt, state)
	} else {
		return ver.uniFactWithIff(newStmt, state)
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
		if env.IsAtomDeclared(ast.NewFcAtom(glob.EmptyPkg, newParam)) {
			newParam = fmt.Sprintf("%s%s", glob.UniPrefix, newParam)
		}
		if param != newParam {
			paramMap[param] = ast.NewFcAtom(glob.EmptyPkg, newParam)
			paramMapStrToStr[param] = newParam
			indexes[i] = newParam
		}
	}
	return paramMap, paramMapStrToStr, indexes
}
