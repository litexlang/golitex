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
	glob "golitex/glob"
	"slices"
)

func (ver *Verifier) matchObjectsWithFreeParamsWithInstObjectsInExistFact(freeParams []string, existFreeParams []string, knownExistParamSets []ast.Obj, givenExistParamSets []ast.Obj, knownExistParamSetsAndParamsInPureFact []ast.Obj, givenExistParamSetsAndParamsInPureFact []ast.Obj) (bool, map[string]ast.Obj) {
	if len(knownExistParamSetsAndParamsInPureFact) != len(givenExistParamSetsAndParamsInPureFact) {
		return false, nil
	}

	if len(knownExistParamSets) != len(givenExistParamSets) {
		return false, nil
	}

	allInstParamsThatEachFreeParamMatchesMap := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsPureFact(freeParams, existFreeParams, knownExistParamSetsAndParamsInPureFact, givenExistParamSetsAndParamsInPureFact)

	allInstParamsThatEachFreeParamMatchesMap2 := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsExistFreeParamSets(freeParams, existFreeParams, knownExistParamSets, givenExistParamSets)

	// merge
	objectsThatEachFreeParamMatches := map[string][]ast.Obj{}
	for _, key := range freeParams {
		curFreeParamMatches := []ast.Obj{}
		if items, ok := allInstParamsThatEachFreeParamMatchesMap[key]; ok {
			curFreeParamMatches = append(curFreeParamMatches, items...)
		}
		if items, ok := allInstParamsThatEachFreeParamMatchesMap2[key]; ok {
			curFreeParamMatches = append(curFreeParamMatches, items...)
		}
		if len(curFreeParamMatches) == 0 {
			return false, nil
		} else {
			objectsThatEachFreeParamMatches[key] = curFreeParamMatches
		}
	}

	// ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualInstParams(mergedInstParamsThatEachFreeParamMatches)
	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualObjects(allInstParamsThatEachFreeParamMatchesMap)
	if !ok {
		return false, nil
	}

	nextState := NewVerState(2, false, true)
	for i, knownParam := range knownExistParamSetsAndParamsInPureFact {
		instKnownParam, err := knownParam.Instantiate(freeParamMatchInstParamMap)
		if err != nil {
			return false, nil
		}
		equalFact := ast.NewEqualFact(instKnownParam, givenExistParamSetsAndParamsInPureFact[i])
		ret := ver.VerFactStmt(equalFact, nextState)
		if ret.IsNotTrue() {
			return false, nil
		}
	}

	return true, freeParamMatchInstParamMap
}

func (ver *Verifier) getAllObjectsThatEachFreeParamMatchesInExistFactByItsPureFact(freeParams []string, existFreeParams []string, knownParams []ast.Obj, givenParams []ast.Obj) map[string][]ast.Obj {
	matchMaps := map[string][]ast.Obj{}
	for _, freeParam := range freeParams {
		matchMaps[freeParam] = []ast.Obj{}
	}

	for i := range len(knownParams) {
		ok, curMatchMap := ver.matchParamWithFreeParamsWithInstParamInExistFactByItsPureFact(freeParams, existFreeParams, knownParams[i], givenParams[i])
		if ok && curMatchMap != nil {
			for key, value := range curMatchMap {
				matchMaps[key] = append(matchMaps[key], value)
			}
		}
	}

	return matchMaps
}

func (ver *Verifier) getAllObjectsThatEachFreeParamMatchesInExistFactByItsExistFreeParamSets(freeParams []string, existFreeParams []string, knownParams []ast.Obj, givenParams []ast.Obj) map[string][]ast.Obj {
	matchMaps := map[string][]ast.Obj{}
	for _, freeParam := range freeParams {
		matchMaps[freeParam] = []ast.Obj{}
	}

	for i := range len(knownParams) {
		ok, curMatchMap := ver.matchObjectWithFreeParamsWithInstObjectInExistFactByItsExistFreeParamSet(freeParams, existFreeParams, knownParams[i], givenParams[i])
		if ok && curMatchMap != nil {
			for key, value := range curMatchMap {
				matchMaps[key] = append(matchMaps[key], value)
			}
		}
	}

	return matchMaps
}

func (ver *Verifier) matchObjectWithFreeParamsWithInstObjectInExistFactByItsExistFreeParamSet(freeParams []string, existFreeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchObjWithFreeParamSetAsAtomWithInstObjSetAsAtomInExistFactByItsExistFreeParamSet(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchObjWithFreeParamsAsAtomWithInstObjAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchObjWithFreeParamsAsFnObjWithInstObjAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchObjWithFreeParamsAsFnObjWithInstObjAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsWithInstParamInExistFactByItsPureFact(freeParams []string, existFreeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchObjWithFreeParamAsAtomWithInstObjAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchObjWithFreeParamsAsAtomWithInstObjAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchObjWithFreeParamsAsFnObjWithInstObjAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchObjWithFreeParamsAsFnObjWithInstObjAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchObjWithFreeParamAsAtomWithInstObjAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	if (string(knownParam) == glob.KeywordSet && string(givenParam) == glob.KeywordSet) || (string(knownParam) == glob.KeywordFiniteSet && string(givenParam) == glob.KeywordFiniteSet) || (string(knownParam) == glob.KeywordNonEmptySet && string(givenParam) == glob.KeywordNonEmptySet) {
		return true, nil
	}

	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
	}

	if slices.Contains(existFreeParams, string(knownParam)) {
		if string(givenParam) == string(knownParam) {
			return true, nil
		}
	}

	equalFact := ast.NewEqualFact(knownParam, givenParam)
	nextState := NewVerState(2, false, false)
	ret := ver.VerFactStmt(equalFact, nextState)
	if ret.IsNotTrue() {
		return false, nil
	} else {
		return true, nil
	}
}

func (ver *Verifier) matchObjWithFreeParamSetAsAtomWithInstObjSetAsAtomInExistFactByItsExistFreeParamSet(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	if (string(knownParam) == glob.KeywordSet && string(givenParam) == glob.KeywordSet) || (string(knownParam) == glob.KeywordFiniteSet && string(givenParam) == glob.KeywordFiniteSet) || (string(knownParam) == glob.KeywordNonEmptySet && string(givenParam) == glob.KeywordNonEmptySet) {
		return true, nil
	}

	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
	}

	if slices.Contains(existFreeParams, string(knownParam)) {
		if string(givenParam) == string(knownParam) {
			return true, nil
		}
	}

	equalFact := ast.NewEqualFact(knownParam, givenParam)
	nextState := NewVerState(2, false, false)
	ret := ver.VerFactStmt(equalFact, nextState)
	if ret.IsNotTrue() {
		return false, nil
	} else {
		return true, nil
	}
}

func (ver *Verifier) matchObjWithFreeParamsAsAtomWithInstObjAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
	}

	if slices.Contains(existFreeParams, string(knownParam)) {
		return false, nil
	}

	equalFact := ast.NewEqualFact(knownParam, givenParam)
	nextState := NewVerState(2, false, false)
	ret := ver.VerFactStmt(equalFact, nextState)
	if ret.IsNotTrue() {
		return false, nil
	} else {
		return true, nil
	}
}

func (ver *Verifier) matchObjWithFreeParamsAsFnObjWithInstObjAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	return false, nil
}

func (ver *Verifier) matchObjWithFreeParamsAsFnObjWithInstObjAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if len(knownParam.Params) != len(givenParam.Params) {
		return false, nil
	}

	if knownParam.FnHead.String() == glob.KeywordSetBuilder || givenParam.FnHead.String() == glob.KeywordSetBuilder {
		return false, nil
	}

	knownParamHead := knownParam.FnHead
	givenParamHead := givenParam.FnHead

	ok, matchMapOfHeads := ver.matchParamWithFreeParamsWithInstParamInExistFactByItsPureFact(freeParams, existFreeParams, knownParamHead, givenParamHead)
	if !ok {
		return false, nil
	}

	allInstParamsThatAFreeParamMatchMap := ver.getAllObjectsThatEachFreeParamMatchesInExistFactByItsPureFact(freeParams, existFreeParams, knownParam.Params, givenParam.Params)

	for key, value := range matchMapOfHeads {
		allInstParamsThatAFreeParamMatchMap[key] = append(allInstParamsThatAFreeParamMatchMap[key], value)
	}

	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualObjects(allInstParamsThatAFreeParamMatchMap)
	if !ok {
		return false, nil
	}

	return true, freeParamMatchInstParamMap
}
