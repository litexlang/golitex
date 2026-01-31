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
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFact_BySpecMem(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	for i := len(ver.Env.EnvSlice) - 1; i >= 0; i-- {
		curEnv := &ver.Env.EnvSlice[i]
		verRet := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.specFact_SpecMem_atEnv(&curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) checkSpecFactUseUniMemAtCurEnv(curEnv *env.EnvMemory, stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	if state.Round == 0 && !state.ReqOk {
		return ast.NewUnknownVerRet(stmt).AddExtraInfo(fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state))
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return ast.NewEmptyUnknownVerRet()
	}

	if _, ok := stmt.(*ast.PureSpecificFactStmt); ok {
		return ver.matchGivenPureFactWithOnesInKnownUniFacts(searchedSpecFacts, stmt.(*ast.PureSpecificFactStmt), state)
	} else {
		return ver.matchGivenExistFactWithOnesInKnownUniFacts(searchedSpecFacts, stmt.(*ast.ExistSpecificFactStmt), state)
	}
}

func (ver *Verifier) matchGivenPureFactWithOnesInKnownUniFacts(knownFacts []env.KnownSpecFact_InUniFact, given *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		newKnownUniFact := ver.Env.GetUniFactFactFreeParamsNotConflictWithDefinedParams(knownFacts[i].UniFact, map[string]struct{}{})

		ret := ver.matchPureFactWithOneInKnownUniFactAndCheckMatchedObjectsSatisfyUniFactConditions(newKnownUniFact, newKnownUniFact.ThenFacts[knownFacts[i].SpecFactIndex].(*ast.PureSpecificFactStmt), given, state)
		if ret.IsTrue() {
			return ret
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) matchGivenExistFactWithOnesInKnownUniFacts(knownFacts []env.KnownSpecFact_InUniFact, given *ast.ExistSpecificFactStmt, state *VerState) ast.VerRet {
	newFreeExistParamsUnused := ver.Env.GenerateNoDuplicateNames(len(given.ExistFreeParams), map[string]struct{}{})
	uniMap := map[string]ast.Obj{}
	usedNamesAsExistFreeParams := map[string]struct{}{}
	for i, givenFreeParam := range given.ExistFreeParams {
		uniMap[givenFreeParam] = ast.Atom(newFreeExistParamsUnused[i])
	}

	newGiven, err := given.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
	if err != nil {
		return ast.NewEmptyVerRetErr()
	}

	for i := len(knownFacts) - 1; i >= 0; i-- {
		newKnownUniFact := ver.Env.GetUniFactFactFreeParamsNotConflictWithDefinedParams(knownFacts[i].UniFact, usedNamesAsExistFreeParams)

		knownExistFactInUni := newKnownUniFact.ThenFacts[knownFacts[i].SpecFactIndex].(*ast.ExistSpecificFactStmt)

		if len(knownExistFactInUni.ExistFreeParams) != len(given.ExistFreeParams) || len(knownExistFactInUni.PureFact.Params) != len(given.PureFact.Params) {
			return ast.NewEmptyUnknownVerRet()
		}

		newKnownExistInUni, err := knownExistFactInUni.ReplaceFreeParamsWithNewParams(newFreeExistParamsUnused)
		if err != nil {
			return ast.NewEmptyVerRetErr()
		}

		ret := ver.matchExistFactWithOneInKnownUniFactAndCheckMatchedObjsSatisfyUniFactConditions(newKnownUniFact, newKnownExistInUni, newGiven, state)
		if ret.IsTrue() {
			return ret
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]ast.Obj, state *VerState) (map[string]ast.Obj, VerRet) {
	newMap := map[string]ast.Obj{}
	for key, value := range paramArrMap {
		if len(value) == 1 {
			newMap[key] = value[0]
			continue
		}

		for i := 1; i < len(value); i++ {
			verRet := ver.objEqualSpec(value[0], value[i], state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return nil, verRet
			}
		}

		newMap[key] = value[0]
	}

	return newMap, glob.NewEmptyVerRetTrue()
}

// func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *env.KnownSpecFact_InLogicExpr, stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {

// 	asStmt, ok := stmt.(*ast.PureSpecificFactStmt)
// 	if !ok {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if len(knownFact.SpecFact.(*ast.PureSpecificFactStmt).Params) != len(asStmt.Params) {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	for i, knownParam := range knownFact.SpecFact.(*ast.PureSpecificFactStmt).Params {
// 		verRet := ver.verEqualBuiltin(knownParam, asStmt.Params[i], state)
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsUnknown() {
// 			verRet := ver.objEqualSpec(knownParam, asStmt.Params[i], state)
// 			if verRet.IsErr() || verRet.IsUnknown() {
// 				return verRet
// 			}
// 		}
// 	}

// 	currentLayerFact := knownFact.LogicExpr

// 	for i, fact := range currentLayerFact.Facts {
// 		if i == int(knownFact.Index) {
// 			continue
// 		}
// 		verRet := ver.VerFactStmt(fact.ReverseIsTrue()[0], state)
// 		if verRet.IsErr() || verRet.IsUnknown() {
// 			return verRet
// 		}
// 	}

// 	if state.WithMsg {
// 		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), []string{knownFact.LogicExpr.String()})
// 	}

// 	return glob.NewEmptyVerRetTrue()
// }

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.EnvMemory, stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			sameEnumPkgPropFacts, memExist := curEnv.KnownFactsStruct.SpecFactMem.PureFacts[string(asFact.PropName)]
			if !memExist {
				return ast.NewEmptyUnknownVerRet()
			}
			return ver.iterateKnownPureSpecFacts_applyObjEqualSpec(asFact, sameEnumPkgPropFacts, state)
		} else {
			sameEnumPkgPropFacts, memExist := curEnv.KnownFactsStruct.SpecFactMem.NotPureFacts[string(asFact.PropName)]
			if !memExist {
				return ast.NewEmptyUnknownVerRet()
			}
			return ver.iterateKnownPureSpecFacts_applyObjEqualSpec(asFact, sameEnumPkgPropFacts, state)
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			sameEnumPkgPropFacts, memExist := curEnv.KnownFactsStruct.SpecFactMem.Exist_St_Facts[string(asFact.GetPropName())]
			if !memExist {
				return ast.NewEmptyUnknownVerRet()
			}
			return ver.iterateKnownExistSpecFacts_applyObjEqualSpec(asFact, sameEnumPkgPropFacts, state)
		} else {
			sameEnumPkgPropFacts, memExist := curEnv.KnownFactsStruct.SpecFactMem.NotExist_St_Facts[string(asFact.GetPropName())]
			if !memExist {
				return ast.NewEmptyUnknownVerRet()
			}
			return ver.iterateKnownExistSpecFacts_applyObjEqualSpec(asFact, sameEnumPkgPropFacts, state)
		}
	}

	// sameEnumFacts, ret := s.getSameEnumFacts(stmt)
	// if ret.IsErr() {
	// 	return nil, false
	// }

	// sameEnumPkgPropFacts, memExist := sameEnumFacts[string(stmt.GetPropName())]
	// if !memExist {
	// 	return nil, false
	// }

	// return sameEnumPkgPropFacts, true

	// knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	// if !got {
	// 	return ast.NewEmptyUnknownVerRet()
	// }

	// if stmt.FactType == ast.TruePure || stmt.FactType == ast.FalsePure {
	// 	return ver.iterateKnownSpecFacts_applyObjEqualSpec(stmt, knownFacts, state)
	// } else {
	// 	return ver.iterateKnownExistFactsAndMatchGivenFact(stmt, knownFacts, state)
	// }
	return ast.NewEmptyUnknownVerRet()
}

// func (ver *Verifier) specFact_LogicMem(curEnv *env.EnvMemory, stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
// 	knownFacts, got := curEnv.KnownFactsStruct.SpecFactInLogicExprMem.GetSameEnumPkgPropFacts(stmt)

// 	if !got {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if got {
// 		for _, knownFact := range knownFacts {
// 			verRet := ver.useKnownOrFactToProveSpecFact(&knownFact, stmt, state)
// 			if verRet.IsErr() {
// 				return verRet
// 			}
// 			if verRet.IsTrue() {
// 				if state.WithMsg {
// 					return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), verRet.VerifyMsgs)
// 				}
// 				return verRet
// 			}
// 		}

// 	}

// 	return ast.NewEmptyUnknownVerRet()
// }

func (ver *Verifier) iterateKnownExistSpecFacts_applyObjEqualSpec(stmt ast.SpecificFactStmt, knownFacts []*ast.ExistSpecificFactStmt, state *VerState) ast.VerRet {
	newParams := ver.Env.GenerateNoDuplicateNames(len(stmt.(*ast.ExistSpecificFactStmt).ExistFreeParams), map[string]struct{}{})

LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.Env.MatchExistSpecificFacts(stmt.(*ast.ExistSpecificFactStmt), knownFact, newParams)
		if verRet.IsErr() {
			return glob.NewVerRet(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{verRet.String()})
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}

		if state.WithMsg {
			return successVerString(stmt, knownFact)
		}
		return glob.NewEmptyVerRetTrue()
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) iterateKnownPureSpecFacts_applyObjEqualSpec(stmt ast.SpecificFactStmt, knownFacts []*ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.matchTwoPureSpecFacts(stmt.(*ast.PureSpecificFactStmt), knownFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}

		if state.WithMsg {
			return successVerString(stmt, knownFact)
		}
		return glob.NewEmptyVerRetTrue()
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) matchTwoPureSpecFacts(stmt *ast.PureSpecificFactStmt, knownFact *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	if len(knownFact.Params) != len(stmt.Params) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 如果不区分 equal 和 其他事实的话，可能会出死循环
	if stmt.PropName == glob.KeySymbolEqual && stmt.IsTrue {
		for i, knownParam := range knownFact.Params {
			verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(knownParam, stmt.Params[i])
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}

	} else {
		newState := state.GetNoMsg()
		for i, knownParam := range knownFact.Params {
			verRet := ver.objEqualSpec(knownParam, stmt.Params[i], newState)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
	}

	return glob.NewEmptyVerRetTrue()
}

// func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
// 	ver.newEnv()
// 	defer ver.deleteEnv()

// 	asStmt, ok := stmt.(*ast.PureSpecificFactStmt)
// 	if !ok {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if asStmt.IsTrue {
// 		verRet := ver.matchTwoPureSpecFacts(asStmt, knownFact.SpecFact.(*ast.PureSpecificFactStmt), state)
// 		if verRet.IsErr() || verRet.IsUnknown() {
// 			return verRet
// 		}
// 	} else {
// 		// ast.VerRet := ver.MatchExistFact(stmt, knownFact.SpecFact, state)
// 		// if verRet.IsErr() || verRet.IsUnknown() {
// 		// 	return verRet
// 		// }
// 		return ast.NewEmptyUnknownVerRet()
// 	}
// 	// ast.VerRet := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
// 	// if verRet.IsErr() || verRet.IsUnknown() {
// 	// 	return verRet
// 	// }

// 	nextState := state.GetAddRound()
// 	for i, fact := range knownFact.LogicExpr.Facts {
// 		if i == knownFact.Index {
// 			continue
// 		}
// 		reversedFact := fact.ReverseIsTrue()[0]
// 		// TODO: WARNING: 这里有问题，可能无限循环
// 		verRet := ver.VerFactStmt(reversedFact, nextState)
// 		if verRet.IsErr() || verRet.IsUnknown() {
// 			return verRet
// 		}
// 	}

// 	if state.WithMsg {
// 		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), []string{knownFact.LogicExpr.String()})
// 	}
// 	return glob.NewEmptyVerRetTrue()
// }

func (ver *Verifier) proveUniFactDomFacts(domFacts []ast.FactStmt, state *VerState) ast.VerRet {
	if !state.isFinalRound() {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(ast.SpecificFactStmt)
			if ok {
				verRet := ver.VerFactStmt(asSpecFact, state.GetFinalRound())
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet
				}
			} else {
				verRet := ver.VerFactStmt(fact, state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet
				}
			}
		}
		return glob.NewEmptyVerRetTrue()
	} else {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(ast.SpecificFactStmt)
			if !ok {
				return ast.NewEmptyUnknownVerRet()
			}
			verRet := ver.VerFactStmt(asSpecFact, state.GetFinalRound())
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
		return glob.NewEmptyVerRetTrue()
	}
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt ast.SpecificFactStmt, orStmt *ast.OrStmt, index int, state *VerState) ast.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	// 其他是否都错
	for i := range orStmt.Facts {
		if i == index {
			continue
		}
		verRet := ver.VerFactStmt(orStmt.Facts[i].ReverseIsTrue()[0], state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		return glob.NewVerRet(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{orStmt.String()})
	}
	return glob.NewEmptyVerRetTrue()
}

// func (ver *Verifier) iterate_KnownPureSpecInUniFacts_applyMatch(stmtToMatch *ast.PureSpecificFactStmt, knownFacts []env.KnownSpecFact_InUniFact, getOkUniConMapErr func([]ast.Obj, []string, []ast.Obj) (bool, map[string]ast.Obj, error), state *VerState) ast.VerRet {
// 	for i := len(knownFacts) - 1; i >= 0; i-- {
// 		knownFact_paramProcessed := knownFacts[i]
// 		// 这里需要用的是 instantiated 的 knownFact

// 		ok, uniConMap, err := getOkUniConMapErr(knownFact_paramProcessed.SpecFact.(*ast.PureSpecificFactStmt).Params, knownFact_paramProcessed.UniFact.Params, stmtToMatch.Params)
// 		if err != nil {
// 			return glob.NewVerRet(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 		}
// 		if !ok {
// 			continue
// 		}

// 		randomizedKnownUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
// 		if err != nil {
// 			return glob.NewVerRet(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 		}

// 		for k, v := range uniConMap {
// 			if newParam, ok := paramMapStrToStr[k]; ok {
// 				uniConMap[newParam] = v
// 				delete(uniConMap, k)
// 			}
// 		}

// 		instantiatedKnownUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedKnownUniFactWithoutThen, uniConMap)
// 		if err != nil {
// 			return glob.NewVerRet(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 		}

// 		var nextState *VerState
// 		if glob.FullMsg {
// 			nextState = state.Copy()
// 		} else {
// 			nextState = state.GetNoMsg()
// 			// nextState = state.Copy()
// 		}

// 		// TODO 要证明在paramSet里
// 		paramInParamSetFacts := instantiatedKnownUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
// 		setFactSatisfied := true
// 		for _, paramInParamSetFact := range paramInParamSetFacts {
// 			verRet := ver.VerFactStmt(paramInParamSetFact, nextState)
// 			if verRet.IsErr() {
// 				return glob.NewVerRet(glob.StmtRetTypeError, paramInParamSetFact.String(), glob.BuiltinLine0, []string{verRet.String()})
// 			}
// 			if verRet.IsUnknown() {
// 				setFactSatisfied = false
// 				break
// 			}
// 		}

// 		if !setFactSatisfied {
// 			continue
// 		}

// 		verRet := ver.proveUniFactDomFacts(instantiatedKnownUniFactWithoutThen.DomFacts, nextState)
// 		if verRet.IsErr() {
// 			return verRet
// 		}

// 		if verRet.IsTrue() {
// 			if state.WithMsg {
// 				return glob.NewVerRet(glob.StmtRetTypeTrue, stmtToMatch.String(), knownFact_paramProcessed.SpecFact.GetLine(), []string{knownFact_paramProcessed.UniFact.String()})
// 			}
// 			return glob.NewEmptyVerRetTrue()
// 		}
// 	}

// 	return ast.NewEmptyUnknownVerRet()
// }

// func (ver *Verifier) iterate_KnownExistSpecInUniFacts_applyMatch_new(stmtToMatch ast.SpecificFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state *VerState) ast.VerRet {
// 	return ast.NewEmptyUnknownVerRet()
// for i := len(knownFacts) - 1; i >= 0; i-- {
// 	knownFact_paramProcessed := knownFacts[i]
// 	// 这里需要用的是 instantiated 的 knownFact

// 	var ok bool
// 	var uniConMap map[string]ast.Obj
// 	var err error
// 	ok, uniConMap, err = ver.matchExistFactWithExistFactInKnownUniFact(&knownFact_paramProcessed, stmtToMatch)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 	}
// 	if !ok {
// 		continue
// 	}

// 	// 后面过程和pure fact一样的

// 	randomizedUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 	}

// 	for k, v := range uniConMap {
// 		if newParam, ok := paramMapStrToStr[k]; ok {
// 			uniConMap[newParam] = v
// 			delete(uniConMap, k)
// 		}
// 	}

// 	instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmtToMatch.String(), glob.BuiltinLine0, []string{err.Error()})
// 	}

// 	var nextState *VerState
// 	if glob.FullMsg {
// 		nextState = state.Copy()
// 	} else {
// 		nextState = state.GetNoMsg()
// 		// nextState = state.Copy()
// 	}

// 	// TODO 要证明在paramSet里
// 	paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
// 	setFactSatisfied := true
// 	for _, paramInParamSetFact := range paramInParamSetFacts {
// 		verRet := ver.VerFactStmt(paramInParamSetFact, nextState)
// 		if verRet.IsErr() {
// 			return glob.NewVerMsg(glob.StmtRetTypeError, paramInParamSetFact.String(), glob.BuiltinLine0, []string{verRet.String()})
// 		}
// 		if verRet.IsUnknown() {
// 			setFactSatisfied = false
// 			break
// 		}
// 	}

// 	if !setFactSatisfied {
// 		continue
// 	}

// 	verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, nextState)
// 	if verRet.IsErr() {
// 		return verRet
// 	}

// 	if verRet.IsTrue() {
// 		if state.WithMsg {
// 			return glob.NewVerMsg(glob.StmtRetTypeTrue, stmtToMatch.String(), knownFact_paramProcessed.SpecFact.GetLine(), []string{knownFact_paramProcessed.UniFact.String()})
// 		}
// 		return glob.NewEmptyVerRetTrue()
// 	}
// }

// return ast.NewEmptyUnknownVerRet()
// }

// func (ver *Verifier) iterate_KnownExistSpecInLogic_InUni_applyMatch_new(stmt ast.SpecificFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state *VerState) ast.VerRet {
// 	return ast.NewEmptyUnknownVerRet()

// for i := len(knownFacts) - 1; i >= 0; i-- {
// 	knownFactUnderLogicExpr := knownFacts[i]
// 	knownFact_paramProcessed := env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}

// 	ok, uniConMap, err := ver.matchExistFactWithExistFactInKnownUniFact(&knownFact_paramProcessed, stmt)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
// 	}
// 	if !ok {
// 		continue
// 	}

// 	randomizedUniFactWithoutThen, _, paramMapStrToStr, randomizedOrStmt, err := ver.preprocessUniFactParamsWithoutThenFacts_OrStmt(knownFactUnderLogicExpr.UniFact, knownFactUnderLogicExpr.LogicExpr)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
// 	}

// 	for k, v := range uniConMap {
// 		if newParam, ok := paramMapStrToStr[k]; ok {
// 			uniConMap[newParam] = v
// 			delete(uniConMap, k)
// 		}
// 	}

// 	instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
// 	}

// 	// insKnownUniFact, err := ast.InstantiateUniFact(knownFactUnderLogicExpr.UniFact, uniConMap)
// 	// if err != nil {
// 	// 	return false, err
// 	// }

// 	// TODO 要证明在paramSet里
// 	// paramInParamSetFacts := insKnownUniFact.ParamInParamSetFacts(uniConMap)
// 	paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
// 	setFactSatisfied := true
// 	for _, paramInParamSetFact := range paramInParamSetFacts {
// 		verRet := ver.VerFactStmt(paramInParamSetFact, state)
// 		if verRet.IsErr() {
// 			return glob.NewVerMsg(glob.StmtRetTypeUnknown, paramInParamSetFact.String(), glob.BuiltinLine0, []string{verRet.String()})
// 		}
// 		if verRet.IsUnknown() {
// 			setFactSatisfied = false
// 			break
// 		}
// 	}

// 	if !setFactSatisfied {
// 		continue
// 	}

// 	// ok, err = ver.proveUniFactDomFacts(insKnownUniFact.DomFacts, state)
// 	verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, state)
// 	if verRet.IsErr() {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
// 	}
// 	if verRet.IsUnknown() {
// 		continue
// 	}

// 	instantiatedLogicExpr, err := randomizedOrStmt.InstantiateFact(uniConMap)
// 	if err != nil {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
// 	}
// 	instantiatedLogicExprAsKnownSpecFact, ok := instantiatedLogicExpr.(*ast.OrStmt)
// 	if !ok {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{"instantiatedLogicExpr is not a KnownSpecFact_InLogicExpr"})
// 	}

// 	verRet = ver.verify_specFact_when_given_orStmt_is_true(stmt, instantiatedLogicExprAsKnownSpecFact, knownFactUnderLogicExpr.Index, state)
// 	if verRet.IsErr() {
// 		return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
// 	}

// 	if verRet.IsTrue() {
// 		if state.WithMsg {
// 			return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{knownFactUnderLogicExpr.UniFact.String()})
// 		}
// 		return glob.NewEmptyVerRetTrue()
// 	}
// }

// return ast.NewEmptyUnknownVerRet()
// }
