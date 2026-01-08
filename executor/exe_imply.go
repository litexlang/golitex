package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (exec *Executor) implyStmt(stmt *ast.ImplyStmt) *glob.StmtRet {
	ver := NewVerifier(exec.Env)

	// 检查涉及到的函数都OK了
	for _, domFact := range stmt.DomFacts {
		switch domFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.checkFnsReq(domFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret.ToStmtRet()
			}
		case *ast.OrStmt:
			panic("")
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		switch thenFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.checkFnsReq(thenFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret.ToStmtRet()
			}
		case *ast.OrStmt:
			panic("")
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		switch thenFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.proveOneThenFactInImplyStmt(stmt, thenFact.(*ast.SpecFactStmt), Round0Msg().UpdateReqOkToTrue())
			if ret.IsNotTrue() {
				return ret
			}
		case *ast.OrStmt:
			panic("")
		}
	}
	return exec.NewTrueStmtRet(stmt)
}

func (ver *Verifier) proveOneThenFactInImplyStmt(stmt *ast.ImplyStmt, thenFact *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.specFact_ImplyMem_atCurEnv(curEnv, stmt, thenFact, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet.ToStmtRet()
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_ImplyMem_atCurEnv(curEnv, stmt, thenFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet.ToStmtRet()
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.specFact_ImplyMem_atCurEnv(&curEnv, stmt, thenFact, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet.ToStmtRet()
		}
	}

	return glob.NewEmptyVerRetUnknown().ToStmtRet()
}

func (ver *Verifier) specFact_ImplyMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.ImplyStmt, fact ast.Spec_OrFact, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), stmt.GetLine(), []string{fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state)})
	}

	searchedKnownFacts := []env.KnownSpecFact_InImplyTemplate{}
	var got bool
	if asSpec, ok := fact.(*ast.SpecFactStmt); ok {
		searchedKnownFacts, got = curEnv.KnownFactsStruct.SpecFactInImplyTemplateMem.GetSameEnumPkgPropFacts(asSpec)
	} else if asOr, ok := fact.(*ast.OrStmt); ok {
		searchedKnownFacts, got = curEnv.KnownFactsStruct.SpecFactInImplyTemplateMem.GetSameEnumPkgPropFacts(asOr.Facts[0])
	} else {
		return glob.NewEmptyVerRetErr()
	}

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	return ver.iterate_KnownPureSpecInImplyStmt_applyMatch(stmt, searchedKnownFacts, fact, state)
}

func (ver *Verifier) iterate_KnownPureSpecInImplyStmt_applyMatch(stmt *ast.ImplyStmt, knownFacts []env.KnownSpecFact_InImplyTemplate, toCheck ast.Spec_OrFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		ok, uniMap, err := ver.matchImplyTemplateParamsWithImplyStmtParams(&knownFacts[i], stmt, toCheck)
		if !ok || err != nil {
			return glob.NewEmptyVerRetUnknown()
		}

		_ = uniMap
	}
	panic("")
}

func (ver *Verifier) matchImplyTemplateParamsWithImplyStmtParams(knownImplyTemplate *env.KnownSpecFact_InImplyTemplate, implyStmt *ast.ImplyStmt, toCheck ast.Spec_OrFact) (bool, map[string]ast.Obj, error) {
	if len(knownImplyTemplate.ImplyTemplate.DomFacts) != len(implyStmt.DomFacts) {
		return false, nil, nil
	}

	matched, uniMap, err := ver.matchImplyTemplateParamsWithAllParamsInImplyStmt(knownImplyTemplate, implyStmt, toCheck)

	if err != nil || matched {
		return matched, uniMap, err
	}

	return false, nil, nil
}

func (ver *Verifier) checkFactTypeAndPropNamesMatch(knownFact ast.Spec_OrFact, implyFact ast.Spec_OrFact) bool {
	switch knownAs := knownFact.(type) {
	case *ast.SpecFactStmt:
		if implyAs, ok := implyFact.(*ast.SpecFactStmt); ok {
			if knownAs.PropName != implyAs.PropName {
				return false
			}
		} else {
			return false
		}
	case *ast.OrStmt:
		if implyAs, ok := implyFact.(*ast.OrStmt); ok {
			if len(implyAs.Facts) != len(knownAs.Facts) {
				return false
			}

			for j := range implyAs.Facts {
				if knownAs.Facts[j].PropName != implyAs.Facts[j].PropName {
					return false
				}
			}

		} else {
			return false
		}
	}
	return true
}

func (ver *Verifier) mergeCurMapToUniMap(curMap map[string]ast.Obj, uniMap map[string]ast.Obj) bool {
	for key, value := range curMap {
		if previousValue, ok := uniMap[key]; ok {
			if ret := ver.VerFactStmt(ast.NewEqualFact(value, previousValue), FinalRoundNoMsg()); ret.IsNotTrue() {
				return false
			}
		} else {
			uniMap[key] = value
		}
	}
	return true
}

func (ver *Verifier) matchDomFactAndMergeToUniMap(knownDomFact ast.Spec_OrFact, implyDomFact ast.Spec_OrFact, knownParams []string, uniMap map[string]ast.Obj) (bool, error) {
	switch implyDomFactAs := implyDomFact.(type) {
	case *ast.SpecFactStmt:
		knownSpecFactAs := knownDomFact.(*ast.SpecFactStmt)
		ok, curMap, err := ver.matchUniFactParamsWithSpecFactParamsInImply(knownSpecFactAs.Params, knownParams, implyDomFactAs)
		if !ok || err != nil {
			return false, err
		}

		if !ver.mergeCurMapToUniMap(curMap, uniMap) {
			return false, nil
		}

	case *ast.OrStmt:
		knownOrFactAs := knownDomFact.(*ast.OrStmt)

		for j := range implyDomFactAs.Facts {
			ok, curMap, err := ver.matchUniFactParamsWithSpecFactParamsInImply(knownOrFactAs.Facts[j].Params, knownParams, implyDomFactAs.Facts[j])
			if !ok || err != nil {
				return false, err
			}

			if !ver.mergeCurMapToUniMap(curMap, uniMap) {
				return false, nil
			}
		}
	}
	return true, nil
}

func (ver *Verifier) matchImplyTemplateParamsWithAllParamsInImplyStmt(knownImplyTemplate *env.KnownSpecFact_InImplyTemplate, implyStmt *ast.ImplyStmt, toCheck ast.Spec_OrFact) (bool, map[string]ast.Obj, error) {
	// 检查所有的prop名对上了
	if len(knownImplyTemplate.ImplyTemplate.DomFacts) != len(implyStmt.DomFacts) {
		return false, nil, nil
	}

	for i, domFact := range knownImplyTemplate.ImplyTemplate.DomFacts {
		if !ver.checkFactTypeAndPropNamesMatch(domFact, implyStmt.DomFacts[i]) {
			return false, nil, nil
		}
	}

	if !ver.checkFactTypeAndPropNamesMatch(knownImplyTemplate.SpecFact, toCheck) {
		return false, nil, nil
	}

	uniMap := map[string]ast.Obj{}
	for i, domFact := range implyStmt.DomFacts {
		ok, err := ver.matchDomFactAndMergeToUniMap(knownImplyTemplate.ImplyTemplate.DomFacts[i], domFact, knownImplyTemplate.ImplyTemplate.Params, uniMap)
		if !ok || err != nil {
			return false, nil, err
		}
	}

	ok, err := ver.matchDomFactAndMergeToUniMap(knownImplyTemplate.SpecFact, toCheck, knownImplyTemplate.ImplyTemplate.Params, uniMap)
	if !ok || err != nil {
		return false, nil, err
	}

	for _, param := range knownImplyTemplate.ImplyTemplate.Params {
		if _, ok := uniMap[param]; !ok {
			return false, nil, nil
		}
	}

	return true, uniMap, nil
}

func (ver *Verifier) matchUniFactParamsWithSpecFactParamsInImply(knownFcs []ast.Obj, freeVars []string, specFact *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
	// knownFcs := knownSpecFactInUniFact.SpecFact.Params
	givenFcs := specFact.Params
	// freeVars := knownSpecFactInUniFact.UniFact.Params
	freeVarsMap := map[string]struct{}{}
	for _, freeVar := range freeVars {
		freeVarsMap[freeVar] = struct{}{}
	}

	matchedMaps, unmatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(knownFcs, givenFcs, freeVarsMap, string(specFact.PropName))
	if err != nil {
		return false, nil, err
	}
	matchedMap, unMatchedFcPairs := ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps, unmatchedFcPairs, map[string][]ast.Obj{}, []fcPair{})

	// 所有自由变量对应的instVar必须相等
	for _, instVars := range matchedMap {
		firstVar := instVars[0]
		for j := 1; j < len(instVars); j++ {
			verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(firstVar, instVars[j]), FinalRoundNoMsg().CopyAndReqOkToTrue())
			if verRet.IsErr() {
				return false, nil, err
			}
			if verRet.IsUnknown() {
				return false, nil, nil
			}
		}
	}

	freeVarToInstVar := map[string]ast.Obj{}
	for freeVar, instVars := range matchedMap {
		freeVarToInstVar[freeVar] = instVars[0]
	}

	// 把实例化了的没被匹配的fcPair拿出来，检查是否是equal
	for _, fcPair := range unMatchedFcPairs {
		instKnownFreeVar, err := fcPair.knownFc.Instantiate(freeVarToInstVar)
		if err != nil {
			return false, nil, err
		}
		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(instKnownFreeVar, fcPair.givenFc), FinalRoundNoMsg().CopyAndReqOkToTrue())

		// REMARK
		// 注：这里err != nil 也是返回 false, 因为有可能会把 sqrt(x) ^ 2 = x 拿来证明 y = z，但是 匹配的时候，可能会导致 x 是 -1 之类的。如果error了，其实就是说明没证明通过
		if verRet.IsErr() || verRet.IsUnknown() {
			return false, nil, nil
		}
	}

	return true, freeVarToInstVar, nil
}
