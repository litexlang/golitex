package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (exec *Executor) inferStmt(stmt *ast.InferStmt) *glob.StmtRet {
	ver := NewVerifier(exec.Env)

	for _, domFact := range stmt.DomFacts {
		ret := exec.factStmt(domFact.(ast.FactStmt))
		if ret.IsNotTrue() {
			return exec.AddStmtToStmtRet(glob.ErrRet(fmt.Sprintf("failed to verify fact: %s", domFact.String())), stmt)
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		ret := ver.proveOneThenFactInImplyStmt(stmt, thenFact, NewVerState(0, true, true))
		if ret.IsNotTrue() {
			return ret
		}
	}

	// emit then
	newFactMsgs := []string{}
	for _, thenFact := range stmt.ThenFacts {
		var factStmt ast.FactStmt
		if specFact, ok := thenFact.(*ast.SpecFactStmt); ok {
			factStmt = specFact
		} else if orStmt, ok := thenFact.(*ast.OrStmt); ok {
			factStmt = orStmt
		} else {
			return glob.ErrRet(fmt.Sprintf("imply statement error: unsupported fact type in thenFacts: %T", thenFact))
		}
		ret := ver.Env.NewFactWithCheckingNameDefined(factStmt)
		if ret.IsNotTrue() {
			return ret
		}
		newFactMsgs = append(newFactMsgs, factStmt.String())
	}

	return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs)
}

func (ver *Verifier) proveOneThenFactInImplyStmt(stmt *ast.InferStmt, thenFact ast.Spec_OrFact, state *VerState) *glob.StmtRet {
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

func (ver *Verifier) specFact_ImplyMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.InferStmt, fact ast.Spec_OrFact, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state)})
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

	return ver.iterate_KnownPureSpecInImplyStmt_applyMatch_InstObjInParamSetAndSatisfyIfFacts(stmt, searchedKnownFacts, fact, state)
}

func (ver *Verifier) iterate_KnownPureSpecInImplyStmt_applyMatch_InstObjInParamSetAndSatisfyIfFacts(stmt *ast.InferStmt, knownFacts []env.KnownSpecFact_InImplyTemplate, toCheck ast.Spec_OrFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		ok, uniMap, err := ver.
			matchImplyTemplateParamsWithAllParamsInImplyStmt(&knownFacts[i], stmt, toCheck)
		if !ok || err != nil {
			return glob.NewEmptyVerRetUnknown()
		}

		localUniMap := map[string]ast.Obj{}

		for j, knownParamSet := range knownFacts[i].ImplyTemplate.ParamSets {
			instKnownParamSet, err := knownParamSet.Instantiate(localUniMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}

			inFact := ast.NewInFactWithObj(uniMap[knownFacts[i].ImplyTemplate.Params[j]], instKnownParamSet)

			ret := ver.VerFactStmt(inFact, state)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}

			localUniMap[knownFacts[i].ImplyTemplate.Params[j]] = uniMap[knownFacts[i].ImplyTemplate.Params[j]]
		}

		for _, ifFact := range knownFacts[i].ImplyTemplate.IfFacts {
			instIfFact, err := ifFact.Instantiate(localUniMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}

			ret := ver.VerFactStmt(instIfFact.(ast.FactStmt), state)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{})
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) checkFactTypeAndPropNamesMatch(knownFact ast.Spec_OrFact, implyFact ast.Spec_OrFact) bool {
	switch knownAs := knownFact.(type) {
	case *ast.SpecFactStmt:
		if implyAs, ok := implyFact.(*ast.SpecFactStmt); ok {
			if knownAs.PropName != implyAs.PropName {
				return false
			}

			if knownAs.FactType != implyAs.FactType {
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
		ok, curMap, err := ver.matchInstSpecFactWithKnownFreeParamsInImply(knownSpecFactAs, knownParams, implyDomFactAs)
		if !ok || err != nil {
			return false, err
		}

		if !ver.mergeCurMapToUniMap(curMap, uniMap) {
			return false, nil
		}

	case *ast.OrStmt:
		knownOrFactAs := knownDomFact.(*ast.OrStmt)

		for j := range implyDomFactAs.Facts {
			ok, curMap, err := ver.matchInstSpecFactWithKnownFreeParamsInImply(knownOrFactAs.Facts[j], knownParams, implyDomFactAs.Facts[j])
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

func (ver *Verifier) matchImplyTemplateParamsWithAllParamsInImplyStmt(knownImplyTemplate *env.KnownSpecFact_InImplyTemplate, implyStmt *ast.InferStmt, toCheck ast.Spec_OrFact) (bool, map[string]ast.Obj, error) {
	// 检查所有的prop名对上了
	if len(knownImplyTemplate.ImplyTemplate.DomFacts) != len(implyStmt.DomFacts) {
		return false, nil, nil
	}

	for i, domFact := range knownImplyTemplate.ImplyTemplate.DomFacts {
		if !ver.checkFactTypeAndPropNamesMatch(domFact, implyStmt.DomFacts[i]) {
			return false, nil, nil
		}
	}

	if !ver.checkFactTypeAndPropNamesMatch(knownImplyTemplate.Spec_orFact, toCheck) {
		return false, nil, nil
	}

	uniMap := map[string]ast.Obj{}
	for i, domFact := range implyStmt.DomFacts {
		ok, err := ver.matchDomFactAndMergeToUniMap(knownImplyTemplate.ImplyTemplate.DomFacts[i], domFact, knownImplyTemplate.ImplyTemplate.Params, uniMap)
		if !ok || err != nil {
			return false, nil, err
		}
	}

	ok, err := ver.matchDomFactAndMergeToUniMap(knownImplyTemplate.Spec_orFact, toCheck, knownImplyTemplate.ImplyTemplate.Params, uniMap)
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

func (ver *Verifier) matchInstSpecFactWithKnownFreeParamsInImply(knownSpecFact *ast.SpecFactStmt, freeVars []string, instFact *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
	if instFact.IsPureFact() {
		return ver.matchUniFactParamsWithSpecFactParamsInImply(knownSpecFact.Params, freeVars, instFact.Params, string(instFact.PropName))
	} else {
		knownExistStruct := knownSpecFact.ToExistStFactStruct()
		instExistStruct := instFact.ToExistStFactStruct()

		// 将 exist 参数全部替换成随机名称，确保不会出问题
		knownExistStruct = ver.replaceExistParamsWithRandomNames(knownExistStruct)
		instExistStruct = ver.replaceExistParamsWithRandomNames(instExistStruct)

		knownFcs := append([]ast.Obj{}, knownExistStruct.ExistFreeParamSets...)
		knownFcs = append(knownFcs, knownExistStruct.Params...)

		instFcs := append([]ast.Obj{}, instExistStruct.ExistFreeParamSets...)
		instFcs = append(instFcs, instExistStruct.Params...)

		return ver.matchUniFactParamsWithSpecFactParamsInImply(knownFcs, freeVars, instFcs, string(knownSpecFact.PropName))
	}
}

func (ver *Verifier) matchUniFactParamsWithSpecFactParamsInImply(knownFcs []ast.Obj, freeVars []string, givenFcs []ast.Obj, propNameForMsg string) (bool, map[string]ast.Obj, error) {
	// knownFcs := knownSpecFactInUniFact.SpecFact.Params
	// freeVars := knownSpecFactInUniFact.UniFact.Params
	freeVarsMap := map[string]struct{}{}
	for _, freeVar := range freeVars {
		freeVarsMap[freeVar] = struct{}{}
	}

	matchedMaps, unmatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(knownFcs, givenFcs, freeVarsMap, string(propNameForMsg))
	if err != nil {
		return false, nil, err
	}
	matchedMap, unMatchedFcPairs := ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps, unmatchedFcPairs, map[string][]ast.Obj{}, []fcPair{})

	// 所有自由变量对应的instVar必须相等
	for _, instVars := range matchedMap {
		firstVar := instVars[0]
		for j := 1; j < len(instVars); j++ {
			verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(firstVar, instVars[j]), FinalRoundNoMsg().CopyAndReqOkToTrue())
			if verRet.IsNotTrue() {
				return false, nil, err
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
		if verRet.IsNotTrue() {
			return false, nil, nil
		}
	}

	return true, freeVarToInstVar, nil
}
