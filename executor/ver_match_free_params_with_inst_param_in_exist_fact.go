package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
)

func (ver *Verifier) matchParamsWithFreeParamsWithInstParamInExistFact(freeParams []string, existFreeParams []string, knownExistParamSetsAndParamsInPureFact []ast.Obj, givenExistParamSetsAndParamsInPureFact []ast.Obj) (bool, map[string]ast.Obj) {
	if len(knownExistParamSetsAndParamsInPureFact) != len(givenExistParamSetsAndParamsInPureFact) {
		return false, nil
	}

	allInstParamsThatEachFreeParamMatchesMap := ver.getAllInstParamsThatEachFreeParamMatchesInExistFact(freeParams, existFreeParams, knownExistParamSetsAndParamsInPureFact, givenExistParamSetsAndParamsInPureFact)

	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualInstParams(allInstParamsThatEachFreeParamMatchesMap)
	if !ok {
		return false, nil
	}

	for i := range len(freeParams) {
		_, ok := freeParamMatchInstParamMap[freeParams[i]]
		if !ok {
			return false, nil
		}
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

func (ver *Verifier) getAllInstParamsThatEachFreeParamMatchesInExistFact(freeParams []string, existFreeParams []string, knownParams []ast.Obj, givenParams []ast.Obj) map[string][]ast.Obj {
	matchMaps := map[string][]ast.Obj{}
	for _, freeParam := range freeParams {
		matchMaps[freeParam] = []ast.Obj{}
	}

	for i := range len(knownParams) {
		ok, curMatchMap := ver.matchParamWithFreeParamsWithInstParamInExistFact(freeParams, existFreeParams, knownParams[i], givenParams[i])
		if ok && curMatchMap != nil {
			for key, value := range curMatchMap {
				matchMaps[key] = append(matchMaps[key], value)
			}
		}
	}

	return matchMaps
}

func (ver *Verifier) matchParamWithFreeParamsWithInstParamInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
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

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
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

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	if len(knownParam.Params) != len(givenParam.Params) {
		return false, nil
	}

	if knownParam.FnHead.String() == glob.KeywordSetBuilder || givenParam.FnHead.String() == glob.KeywordSetBuilder {
		return false, nil
	}

	knownParamHead := knownParam.FnHead
	givenParamHead := givenParam.FnHead

	ok, matchMapOfHeads := ver.matchParamWithFreeParamsWithInstParamInExistFact(freeParams, existFreeParams, knownParamHead, givenParamHead)
	if !ok {
		return false, nil
	}

	allInstParamsThatAFreeParamMatchMap := ver.getAllInstParamsThatEachFreeParamMatchesInExistFact(freeParams, existFreeParams, knownParam.Params, givenParam.Params)

	for key, value := range matchMapOfHeads {
		allInstParamsThatAFreeParamMatchMap[key] = append(allInstParamsThatAFreeParamMatchMap[key], value)
	}

	ok, freeParamMatchInstParamMap := ver.checkEachFreeParamMatchesEqualInstParams(allInstParamsThatAFreeParamMatchMap)
	if !ok {
		return false, nil
	}

	return true, freeParamMatchInstParamMap
}
