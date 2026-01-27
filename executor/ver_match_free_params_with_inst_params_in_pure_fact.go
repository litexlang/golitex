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

func (ver *Verifier) matchParamsWithFreeParamsWithInstParamInPureFact(freeParams []string, knownParams []ast.Obj, givenParams []ast.Obj) (bool, map[string]ast.Obj) {
	if len(knownParams) != len(givenParams) {
		return false, nil
	}

	allInstParamsThatEachFreeParamMatchesMap := ver.getAllInstParamsThatEachFreeParamMatchesInPureFact(freeParams, knownParams, givenParams)

	for i := range len(freeParams) {
		items, ok := allInstParamsThatEachFreeParamMatchesMap[freeParams[i]]
		if !ok || len(items) == 0 {
			return false, nil
		}
	}

	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualInstParams(allInstParamsThatEachFreeParamMatchesMap)
	if !ok {
		return false, nil
	}

	// known parameters must equal to given parameters
	// nextState := NewVerState(2, false, false)
	nextState := NewVerState(2, false, true)
	for i, knownParam := range knownParams {
		instKnownParam, err := knownParam.Instantiate(freeParamMatchInstParamMap)
		if err != nil {
			return false, nil
		}
		equalFact := ast.NewEqualFact(instKnownParam, givenParams[i])
		ret := ver.VerFactStmt(equalFact, nextState)
		if ret.IsNotTrue() {
			return false, nil
		}
	}

	return true, freeParamMatchInstParamMap
}

func (ver *Verifier) checkEachFreeParamMatchesEqualInstParams(allInstParamsThatAFreeParamMatchMap map[string][]ast.Obj) (bool, map[string]ast.Obj) {
	retMatchMap := map[string]ast.Obj{}
	nextState := NewVerState(2, false, false)

	for freeParamName, instParamsMatchFreeParam := range allInstParamsThatAFreeParamMatchMap {
		if len(instParamsMatchFreeParam) == 0 {
			continue
		}

		if len(instParamsMatchFreeParam) == 1 {
			retMatchMap[freeParamName] = instParamsMatchFreeParam[0]
		}

		for i := 1; i < len(instParamsMatchFreeParam); i++ {
			equalFact := ast.NewEqualFact(instParamsMatchFreeParam[0], instParamsMatchFreeParam[i])
			ret := ver.VerFactStmt(equalFact, nextState)
			if ret.IsNotTrue() {
				return false, nil
			}
		}

		retMatchMap[freeParamName] = instParamsMatchFreeParam[0]
	}

	return true, retMatchMap
}

func (ver *Verifier) getAllInstParamsThatEachFreeParamMatchesInPureFact(freeParams []string, knownParams []ast.Obj, givenParams []ast.Obj) map[string][]ast.Obj {
	matchMaps := map[string][]ast.Obj{}
	for _, freeParam := range freeParams {
		matchMaps[freeParam] = []ast.Obj{}
	}

	for i := range len(knownParams) {
		ok, curMatchMap := ver.matchParamWithFreeParamsWithInstParamInPureFact(freeParams, knownParams[i], givenParams[i])
		if ok && curMatchMap != nil {
			for key, value := range curMatchMap {
				matchMaps[key] = append(matchMaps[key], value)
			}
		}
	}

	return matchMaps
}

func (ver *Verifier) matchParamWithFreeParamsWithInstParamInPureFact(freeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsAtomInPureFact(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInPureFact(freeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInPureFact(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInPureFact(freeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsAtomInPureFact(freeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
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

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInPureFact(freeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
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

// 如果 knownParam 里含有 未申明的freeParams 那返回值一定是 false,因为没申明的东西会在check fn req 的时候出错
func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInPureFact(freeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	return false, nil
	// equalFact := ast.NewEqualFact(knownParam, givenParam)
	// nextState := NewVerState(2, false, false)
	// ret := ver.VerFactStmt(equalFact, nextState)
	// if ret.IsNotTrue() {
	// 	return false, nil
	// } else {
	// 	return true, nil
	// }
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInPureFact(freeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if len(knownParam.Params) != len(givenParam.Params) {
		return false, nil
	}

	if knownParam.FnHead.String() == glob.KeywordSetBuilder || givenParam.FnHead.String() == glob.KeywordSetBuilder {
		return false, nil
	}

	knownParamHead := knownParam.FnHead
	givenParamHead := givenParam.FnHead

	ok, matchMapOfHeads := ver.matchParamWithFreeParamsWithInstParamInPureFact(freeParams, knownParamHead, givenParamHead)
	if !ok {
		return false, nil
	}

	allInstParamsThatAFreeParamMatchMap := ver.getAllInstParamsThatEachFreeParamMatchesInPureFact(freeParams, knownParam.Params, givenParam.Params)

	for key, value := range matchMapOfHeads {
		allInstParamsThatAFreeParamMatchMap[key] = append(allInstParamsThatAFreeParamMatchMap[key], value)
	}

	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualInstParams(allInstParamsThatAFreeParamMatchMap)
	if !ok {
		return false, nil
	}

	return true, freeParamMatchInstParamMap
}
