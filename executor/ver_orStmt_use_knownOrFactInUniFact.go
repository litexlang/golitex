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
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verOrStmtByUniFactMem(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	nextState := state.GetAddRound()

	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.verOrFactByUniFactMemAtEnv(curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.verOrFactByUniFactMemAtEnv(curEnv, stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.verOrFactByUniFactMemAtEnv(&curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verOrFactByUniFactMemAtEnv(curEnv *env.EnvMemory, stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	key := string(stmt.Facts[0].GetPropName())
	knownOrFacts, got := curEnv.OrFactInUniFactMem[key]
	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	for _, knownOrFactInUniFact := range knownOrFacts {
		ret := ver.useKnownOrFactInUniFactToCheckGivenOrFact(stmt, knownOrFactInUniFact, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) useKnownOrFactInUniFactToCheckGivenOrFact(given *ast.OrStmt, knownOrFactInUni *env.OrFactInUniFact, state *VerState) *glob.VerRet {
	if len(given.Facts) != len(knownOrFactInUni.OrFact.Facts) {
		return glob.NewEmptyVerRetUnknown()
	}

	for i := range given.Facts {
		if given.Facts[i].GetPropName().String() != knownOrFactInUni.OrFact.Facts[i].GetPropName().String() || given.Facts[i].GetFactType() != knownOrFactInUni.OrFact.Facts[i].GetFactType() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewUnknownVerRet("")

	freeParamObjMap := map[string]ast.Obj{}

	// 让dom和paramSet都成立
	for _, domFact := range knownOrFactInUni.UniFact.DomFacts {
		instDomFact, err := domFact.Instantiate(freeParamObjMap)
		if err != nil {
			return glob.NewVerRet(glob.StmtRetTypeError, domFact.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		verRet := ver.VerFactStmt(instDomFact.(ast.FactStmt), state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	newUniMap := map[string]ast.Obj{}
	for i, paramSet := range knownOrFactInUni.UniFact.ParamSets {
		instParamSet, err := paramSet.Instantiate(newUniMap)
		if err != nil {
			return glob.NewVerRet(glob.StmtRetTypeError, paramSet.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(freeParamObjMap[knownOrFactInUni.UniFact.Params[i]], instParamSet.(ast.Obj)), state)
		if verRet.IsNotTrue() {
			return verRet
		}
		newUniMap[knownOrFactInUni.UniFact.Params[i]] = freeParamObjMap[knownOrFactInUni.UniFact.Params[i]]
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) matchOrFactWithOneInKnownUniFact(knownUniFact *ast.UniFactStmt, orFactInKnownUniFact *ast.OrStmt, given *ast.OrStmt) *glob.VerRet {
	freeParamObjMaps := map[string][]ast.Obj{}
	for _, key := range knownUniFact.Params {
		freeParamObjMaps[key] = []ast.Obj{}
	}

	for i, curGiven := range given.Facts {
		curKnown := orFactInKnownUniFact.Facts[i]

		switch curKnownAs := curKnown.(type) {
		case *ast.PureSpecificFactStmt:
			curGivenAs := curGiven.(*ast.PureSpecificFactStmt)
			allInstParamsThatEachFreeParamMatchesMap := ver.getAllObjectsThatEachFreeParamMatchesInPureFact(knownUniFact.Params, curKnownAs.Params, curGivenAs.Params)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}
		case *ast.ExistSpecificFactStmt:
			curGivenAs := curGiven.(*ast.ExistSpecificFactStmt)

			newFreeExistParamsUnused := ver.Env.GenerateNoDuplicateNames(len(curGivenAs.ExistFreeParams), map[string]struct{}{})

			newCurGiven, err := curGivenAs.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
			if err != nil {
				return glob.NewEmptyVerRetErr()
			}

			newCurKnown, err := curKnownAs.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
			if err != nil {
				return glob.NewEmptyVerRetErr()
			}

			allInstParamsThatEachFreeParamMatchesMap := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsPureFact(knownUniFact.Params, newCurGiven.ExistFreeParams, newCurKnown.PureFact.Params, newCurGiven.PureFact.Params)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}

			allInstParamsThatEachFreeParamMatchesMap2 := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsExistFreeParamSets(knownUniFact.Params, newCurGiven.ExistFreeParams, newCurKnown.ExistFreeParamSets, newCurGiven.ExistFreeParamSets)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap2 {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}
