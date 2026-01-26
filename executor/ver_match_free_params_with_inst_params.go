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

func (ver *Verifier) matchParamWithFreeParamsWithInstParam(freeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsAtom(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsFnObj(freeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsAtom(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsFnObj(freeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsAtom(freeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
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

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsFnObj(freeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
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
func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsAtom(freeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	equalFact := ast.NewEqualFact(knownParam, givenParam)
	nextState := NewVerState(2, false, false)
	ret := ver.VerFactStmt(equalFact, nextState)
	if ret.IsNotTrue() {
		return false, nil
	} else {
		return true, nil
	}
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsFnObj(freeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if len(knownParam.Params) != len(givenParam.Params) {
		return false, nil
	}

	if knownParam.FnHead.String() == glob.KeywordSetBuilder || givenParam.FnHead.String() == glob.KeywordSetBuilder {
		return false, nil
	}

	knownParamHead := knownParam.FnHead
	givenParamHead := givenParam.FnHead

	ok, matchMapOfHeads := ver.matchParamWithFreeParamsWithInstParam(freeParams, knownParamHead, givenParamHead)
	if !ok {
		return false, nil
	}

	matchMaps := map[string][]ast.Obj{}
	for _, freeParam := range freeParams {
		matchMaps[freeParam] = []ast.Obj{}
	}

	for key, value := range matchMapOfHeads {
		matchMaps[key] = append(matchMaps[key], value)
	}

	for i := range len(knownParam.Params) {
		ok, curMatchMap := ver.matchParamWithFreeParamsWithInstParam(freeParams, knownParam.Params[i], givenParam.Params[i])
		if ok && curMatchMap != nil {
			for key, value := range curMatchMap {
				matchMaps[key] = append(matchMaps[key], value)
			}
		}
	}

	retMatchMap := map[string]ast.Obj{}
	for freeParamName, instParamsMatchFreeParam := range matchMaps {
		if len(instParamsMatchFreeParam) == 0 {
			continue
		}

		if len(instParamsMatchFreeParam) == 1 {
			retMatchMap[freeParamName] = instParamsMatchFreeParam[0]
		}

		nextState := NewVerState(2, false, false)
		for i := 1; i < len(instParamsMatchFreeParam); i++ {
			equalFact := ast.NewEqualFact(instParamsMatchFreeParam[0], instParamsMatchFreeParam[i])
			ret := ver.VerFactStmt(equalFact, nextState)
			if ret.IsNotTrue() {
				return false, nil
			}
		}
	}

	return true, retMatchMap
}
