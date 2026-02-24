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
)

func (ver *Verifier) verOrStmtByUniFactMem(stmt *ast.OrStmt, state *VerState) ast.VerRet {
	nextState := state.GetAddRound()

	// 生成 given facts 的所有排列
	permutations := generatePermutations(stmt.Facts)

	// 对每个排列尝试匹配
	for _, perm := range permutations {
		reorderedStmt := ast.NewOrStmt(perm, stmt.Line)

		for curEnvIndex := range ver.Env.EnvSlice {
			curEnv := &ver.Env.EnvSlice[curEnvIndex]
			verRet := ver.verOrFactByUniFactMemAtEnv(curEnv, reorderedStmt, nextState)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}

		curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
		verRet := ver.verOrFactByUniFactMemAtEnv(curEnv, reorderedStmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
			curEnv := pkgEnvMgr.EnvSlice[0]
			verRet := ver.verOrFactByUniFactMemAtEnv(&curEnv, reorderedStmt, nextState)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verOrFactByUniFactMemAtEnv(curEnv *env.EnvMemory, stmt *ast.OrStmt, state *VerState) ast.VerRet {
	key := string(stmt.Facts[0].Key())
	knownOrFacts, got := curEnv.OrFactInUniFactMem[key]
	if !got {
		return ast.NewEmptyUnknownVerRet()
	}

	for _, knownOrFactInUniFact := range knownOrFacts {
		ret := ver.useKnownOrFactInUniFactToCheckGivenOrFact(stmt, knownOrFactInUniFact, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) useKnownOrFactInUniFactToCheckGivenOrFact(given *ast.OrStmt, knownOrFactInUni *env.OrFactInUniFact, state *VerState) ast.VerRet {
	if len(given.Facts) != len(knownOrFactInUni.OrFact.Facts) {
		return ast.NewEmptyUnknownVerRet()
	}

	ok, freeParamObjMap := ver.matchOrFactWithOneInKnownUniFact(knownOrFactInUni.UniFact, knownOrFactInUni.OrFact, given, state)
	if ok {
		// 验证 dom 和 paramSet
		verRet := ver.verifyDomAndParamSets(knownOrFactInUni, freeParamObjMap, state)
		if verRet.IsTrue() {
			return ast.NewTrueVerRet(given, nil, knownOrFactInUni.UniFact.String())
		}
		if verRet.IsErr() {
			return verRet
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

// verifyDomAndParamSets 验证 dom 和 paramSet 是否成立
func (ver *Verifier) verifyDomAndParamSets(knownOrFactInUni *env.OrFactInUniFact, freeParamObjMap map[string]ast.Obj, state *VerState) ast.VerRet {
	// 让dom和paramSet都成立
	for _, domFact := range knownOrFactInUni.UniFact.DomFacts {
		instDomFact, err := domFact.Instantiate(freeParamObjMap)
		if err != nil {
			return ast.NewErrVerRet(domFact).AddExtraInfo(err.Error())
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
			return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
		}
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(freeParamObjMap[knownOrFactInUni.UniFact.Params[i]], instParamSet.(ast.Obj)), state)
		if verRet.IsNotTrue() {
			return verRet
		}
		newUniMap[knownOrFactInUni.UniFact.Params[i]] = freeParamObjMap[knownOrFactInUni.UniFact.Params[i]]
	}

	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) matchOrFactWithOneInKnownUniFact(knownUniFact *ast.UniFactStmt, orFactInKnownUniFact *ast.OrStmt, given *ast.OrStmt, state *VerState) (bool, map[string]ast.Obj) {
	freeParamObjMaps := map[string][]ast.Obj{}
	for _, key := range knownUniFact.Params {
		freeParamObjMaps[key] = []ast.Obj{}
	}

	for i, curGiven := range given.Facts {
		curKnown := orFactInKnownUniFact.Facts[i]

		switch curKnownAs := curKnown.(type) {
		case *ast.PureSpecificFactStmt:
			curGivenAs, ok := curGiven.(*ast.PureSpecificFactStmt)
			if !ok {
				return false, nil
			}
			allInstParamsThatEachFreeParamMatchesMap := ver.getAllObjectsThatEachFreeParamMatchesInPureFact(knownUniFact.Params, curKnownAs.Params, curGivenAs.Params)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}
		case *ast.ExistSpecificFactStmt:
			curGivenAs, ok := curGiven.(*ast.ExistSpecificFactStmt)
			if !ok {
				return false, nil
			}

			if len(curGivenAs.PureFact) != len(curKnownAs.PureFact) {
				return false, nil
			}

			for j := range curGivenAs.PureFact {
				if curGivenAs.PureFact[j].IsTrue != curKnownAs.PureFact[j].IsTrue {
					return false, nil
				}
			}

			newFreeExistParamsUnused := ver.Env.GenerateNoDuplicateNames(len(curGivenAs.ExistFreeParams), map[string]struct{}{})

			newCurGiven, err := curGivenAs.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
			if err != nil {
				return false, nil
			}

			newCurKnown, err := curKnownAs.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
			if err != nil {
				return false, nil
			}

			allParamsInNewCurKnown := []ast.Obj{}
			for _, fact := range newCurKnown.PureFact {
				allParamsInNewCurKnown = append(allParamsInNewCurKnown, fact.Params...)
			}

			allParamsInNewCurGiven := []ast.Obj{}
			for _, fact := range newCurGiven.PureFact {
				allParamsInNewCurGiven = append(allParamsInNewCurGiven, fact.Params...)
			}

			allInstParamsThatEachFreeParamMatchesMap := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsPureFact(knownUniFact.Params, newCurGiven.ExistFreeParams, allParamsInNewCurKnown, allParamsInNewCurGiven)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}

			allInstParamsThatEachFreeParamMatchesMap2 := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsExistFreeParamSets(knownUniFact.Params, newCurGiven.ExistFreeParams, newCurKnown.ExistFreeParamSets, newCurGiven.ExistFreeParamSets)
			for key, value := range allInstParamsThatEachFreeParamMatchesMap2 {
				freeParamObjMaps[key] = append(freeParamObjMaps[key], value...)
			}
		}
	}

	// All free params must match some inst params and those inst params must be equal
	for _, key := range knownUniFact.Params {
		if _, ok := freeParamObjMaps[key]; !ok || len(freeParamObjMaps[key]) == 0 {
			return false, nil
		}

		for j := 1; j < len(freeParamObjMaps[key]); j++ {
			equalFact := ast.NewEqualFact(freeParamObjMaps[key][0], freeParamObjMaps[key][j])
			ret := ver.VerFactStmt(equalFact, state)
			if ret.IsNotTrue() {
				return false, nil
			}
		}
	}

	freeParamObjMap := map[string]ast.Obj{}
	for key, value := range freeParamObjMaps {
		freeParamObjMap[key] = value[0]
	}
	return true, freeParamObjMap
}
