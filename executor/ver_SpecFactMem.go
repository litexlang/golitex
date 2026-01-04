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
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFact_BySpecMem(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	defInCurEnvPkgMgr, ok := ver.Env.GetPropDef(stmt.PropName)
	if ok {
		for i := len(ver.Env.EnvSlice) - 1; i >= defInCurEnvPkgMgr.EnvDepth; i-- {
			curEnv := &ver.Env.EnvSlice[i]
			verRet := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}

		return glob.NewEmptyVerRetUnknown()
	} else {
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

	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact_ByLogicMem(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	nextState := state.GetAddRound()
	// Add builtin env check
	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_LogicMem(curEnv, stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	// if ver.env.CurMatchProp == nil {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.specFact_LogicMem(curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact_InSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.specFact_UniMem_atCurEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_UniMem_atCurEnv(curEnv, stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.specFact_UniMem_atCurEnv(&curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact_InLogicExpr_InUniFactMem(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.specFact_inLogicExpr_inUniFactMem_atEnv(&curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) specFact_inLogicExpr_inUniFactMem_atEnv(curEnv *env.EnvMemory, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	nextState := state.GetAddRound()

	if stmt.IsPureFact() {
		return ver.iterate_KnownPureSpecInLogic_InUni_applyMatch_new(stmt, searchedSpecFactsInLogicExpr, nextState)
	} else {
		return ver.iterate_KnownExistSpecInLogic_InUni_applyMatch_new(stmt, searchedSpecFactsInLogicExpr, nextState)
	}
}

func (ver *Verifier) iterate_KnownPureSpecInLogic_InUni_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFactUnderLogicExpr := knownFacts[i]
		knownFact_paramProcessed := env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}

		ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmt)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, randomizedOrStmt, err := ver.preprocessUniFactParamsWithoutThenFacts_OrStmt(knownFactUnderLogicExpr.UniFact, knownFactUnderLogicExpr.LogicExpr)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}

		// insKnownUniFact, err := ast.InstantiateUniFact(knownFactUnderLogicExpr.UniFact, uniConMap)
		// if err != nil {
		// 	return false, err
		// }

		// TODO 要证明在paramSet里
		// paramInParamSetFacts := insKnownUniFact.ParamInParamSetFacts(uniConMap)
		paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
		setFactSatisfied := true
		for _, paramInParamSetFact := range paramInParamSetFacts {
			verRet := ver.VerFactStmt(paramInParamSetFact, state)
			if verRet.IsErr() {
				return glob.NewVerMsg2(glob.StmtRetTypeUnknown, paramInParamSetFact.String(), paramInParamSetFact.GetLine(), []string{verRet.String()})
			}
			if verRet.IsUnknown() {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		// ok, err = ver.proveUniFactDomFacts(insKnownUniFact.DomFacts, state)
		verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, state)
		if verRet.IsErr() {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
		}
		if verRet.IsUnknown() {
			continue
		}

		instantiatedLogicExpr, err := randomizedOrStmt.InstantiateFact(uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}
		instantiatedLogicExprAsKnownSpecFact, ok := instantiatedLogicExpr.(*ast.OrStmt)
		if !ok {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{"instantiatedLogicExpr is not a KnownSpecFact_InLogicExpr"})
		}

		verRet = ver.verify_specFact_when_given_orStmt_is_true(stmt, instantiatedLogicExprAsKnownSpecFact, knownFactUnderLogicExpr.Index, state)
		if verRet.IsErr() {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
		}

		if verRet.IsTrue() {
			if state.WithMsg {
				return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{knownFactUnderLogicExpr.UniFact.String()})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) specFact_UniMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if state.Round == 0 && !state.ReqOk {
		return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), stmt.GetLine(), []string{fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state)})
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	// return ver.iterate_KnownSpecInUniFacts_applyMatch(stmt, searchedSpecFacts, state)
	if stmt.IsPureFact() {
		return ver.iterate_KnownPureSpecInUniFacts_applyMatch_new(stmt, searchedSpecFacts, state)
	} else {
		return ver.iterate_KnownExistSpecInUniFacts_applyMatch_new(stmt, searchedSpecFacts, state)
	}
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]ast.Obj, state *VerState) (map[string]ast.Obj, *glob.VerRet) {
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

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if len(knownFact.SpecFact.Params) != len(stmt.Params) {
		return glob.NewEmptyVerRetUnknown()
	}

	for i, knownParam := range knownFact.SpecFact.Params {
		verRet := ver.verEqualBuiltin(knownParam, stmt.Params[i], state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			verRet := ver.objEqualSpec(knownParam, stmt.Params[i], state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
	}

	currentLayerFact := knownFact.LogicExpr

	for i, fact := range currentLayerFact.Facts {
		if i == int(knownFact.Index) {
			continue
		}
		verRet := ver.VerFactStmt(fact.ReverseTrue(), state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), []string{knownFact.LogicExpr.String()})
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.EnvMemory, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	if stmt.FactType == ast.TruePure || stmt.FactType == ast.FalsePure {
		return ver.iterateKnownSpecFacts_applyObjEqualSpec(stmt, knownFacts, state)
	} else {
		return ver.iterateKnownExistFactsAndMatchGivenFact(stmt, knownFacts, state)
	}
}

func (ver *Verifier) specFact_LogicMem(curEnv *env.EnvMemory, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactInLogicExprMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	if got {
		for _, knownFact := range knownFacts {
			verRet := ver.useKnownOrFactToProveSpecFact(&knownFact, stmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				if state.WithMsg {
					return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), verRet.VerifyMsgs)
				}
				return verRet
			}
		}

	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) iterateKnownSpecFacts_applyObjEqualSpec(stmt *ast.SpecFactStmt, knownFacts []ast.SpecFactStmt, state *VerState) *glob.VerRet {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.matchTwoSpecFacts(stmt, &knownFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}

		if state.WithMsg {
			return successVerString(stmt, &knownFact)
		}
		return glob.NewEmptyVerRetTrue()
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) matchTwoSpecFacts(stmt *ast.SpecFactStmt, knownFact *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if len(knownFact.Params) != len(stmt.Params) || knownFact.FactType != stmt.FactType {
		return glob.NewEmptyVerRetUnknown()
	}

	// 如果不区分 equal 和 其他事实的话，可能会出死循环
	if stmt.PropName == glob.KeySymbolEqual && stmt.IsTrue() {
		for i, knownParam := range knownFact.Params {
			verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(knownParam, stmt.Params[i], state)
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

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	if stmt.FactType == ast.TruePure || stmt.FactType == ast.FalsePure {
		verRet := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	} else {
		verRet := ver.MatchExistFact(stmt, knownFact.SpecFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}
	// verRet := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
	// if verRet.IsErr() || verRet.IsUnknown() {
	// 	return verRet
	// }

	nextState := state.GetAddRound()
	for i, fact := range knownFact.LogicExpr.Facts {
		if i == knownFact.Index {
			continue
		}
		reversedFact := fact.ReverseTrue()
		// TODO: WARNING: 这里有问题，可能无限循环
		verRet := ver.VerFactStmt(reversedFact, nextState)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), knownFact.SpecFact.GetLine(), []string{knownFact.LogicExpr.String()})
	}
	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) proveUniFactDomFacts(domFacts []ast.FactStmt, state *VerState) *glob.VerRet {
	if !state.isFinalRound() {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
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
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if !ok {
				return glob.NewEmptyVerRetUnknown()
			}
			verRet := ver.VerFactStmt(asSpecFact, state.GetFinalRound())
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
		return glob.NewEmptyVerRetTrue()
	}
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state *VerState) *glob.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	// 其他是否都错
	for i := range orStmt.Facts {
		if i == index {
			continue
		}
		verRet := ver.VerFactStmt(orStmt.Facts[i].ReverseTrue(), state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), stmt.GetLine(), []string{orStmt.String()})
	}
	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) iterate_KnownPureSpecInUniFacts_applyMatch_new(stmtToMatch *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFact_paramProcessed := knownFacts[i]
		// 这里需要用的是 instantiated 的 knownFact

		var ok bool
		var uniConMap map[string]ast.Obj
		var err error
		ok, uniConMap, err = ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmtToMatch)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}

		var nextState *VerState
		if glob.FullMsg {
			nextState = state.Copy()
		} else {
			nextState = state.GetNoMsg()
			// nextState = state.Copy()
		}

		// TODO 要证明在paramSet里
		paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
		setFactSatisfied := true
		for _, paramInParamSetFact := range paramInParamSetFacts {
			verRet := ver.VerFactStmt(paramInParamSetFact, nextState)
			if verRet.IsErr() {
				return glob.NewVerMsg2(glob.StmtRetTypeError, paramInParamSetFact.String(), paramInParamSetFact.GetLine(), []string{verRet.String()})
			}
			if verRet.IsUnknown() {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, nextState)
		if verRet.IsErr() {
			return verRet
		}

		if verRet.IsTrue() {
			if state.WithMsg {
				return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmtToMatch.String(), knownFact_paramProcessed.SpecFact.GetLine(), []string{knownFact_paramProcessed.UniFact.String()})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) iterate_KnownExistSpecInUniFacts_applyMatch_new(stmtToMatch *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFact_paramProcessed := knownFacts[i]
		// 这里需要用的是 instantiated 的 knownFact

		var ok bool
		var uniConMap map[string]ast.Obj
		var err error
		ok, uniConMap, err = ver.matchExistFactWithExistFactInKnownUniFact(&knownFact_paramProcessed, stmtToMatch)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}
		if !ok {
			continue
		}

		// 后面过程和pure fact一样的

		randomizedUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmtToMatch.String(), stmtToMatch.GetLine(), []string{err.Error()})
		}

		var nextState *VerState
		if glob.FullMsg {
			nextState = state.Copy()
		} else {
			nextState = state.GetNoMsg()
			// nextState = state.Copy()
		}

		// TODO 要证明在paramSet里
		paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
		setFactSatisfied := true
		for _, paramInParamSetFact := range paramInParamSetFacts {
			verRet := ver.VerFactStmt(paramInParamSetFact, nextState)
			if verRet.IsErr() {
				return glob.NewVerMsg2(glob.StmtRetTypeError, paramInParamSetFact.String(), paramInParamSetFact.GetLine(), []string{verRet.String()})
			}
			if verRet.IsUnknown() {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, nextState)
		if verRet.IsErr() {
			return verRet
		}

		if verRet.IsTrue() {
			if state.WithMsg {
				return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmtToMatch.String(), knownFact_paramProcessed.SpecFact.GetLine(), []string{knownFact_paramProcessed.UniFact.String()})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) iterate_KnownExistSpecInLogic_InUni_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state *VerState) *glob.VerRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFactUnderLogicExpr := knownFacts[i]
		knownFact_paramProcessed := env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}

		ok, uniConMap, err := ver.matchExistFactWithExistFactInKnownUniFact(&knownFact_paramProcessed, stmt)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, randomizedOrStmt, err := ver.preprocessUniFactParamsWithoutThenFacts_OrStmt(knownFactUnderLogicExpr.UniFact, knownFactUnderLogicExpr.LogicExpr)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}

		// insKnownUniFact, err := ast.InstantiateUniFact(knownFactUnderLogicExpr.UniFact, uniConMap)
		// if err != nil {
		// 	return false, err
		// }

		// TODO 要证明在paramSet里
		// paramInParamSetFacts := insKnownUniFact.ParamInParamSetFacts(uniConMap)
		paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
		setFactSatisfied := true
		for _, paramInParamSetFact := range paramInParamSetFacts {
			verRet := ver.VerFactStmt(paramInParamSetFact, state)
			if verRet.IsErr() {
				return glob.NewVerMsg2(glob.StmtRetTypeUnknown, paramInParamSetFact.String(), paramInParamSetFact.GetLine(), []string{verRet.String()})
			}
			if verRet.IsUnknown() {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		// ok, err = ver.proveUniFactDomFacts(insKnownUniFact.DomFacts, state)
		verRet := ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, state)
		if verRet.IsErr() {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
		}
		if verRet.IsUnknown() {
			continue
		}

		instantiatedLogicExpr, err := randomizedOrStmt.InstantiateFact(uniConMap)
		if err != nil {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{err.Error()})
		}
		instantiatedLogicExprAsKnownSpecFact, ok := instantiatedLogicExpr.(*ast.OrStmt)
		if !ok {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{"instantiatedLogicExpr is not a KnownSpecFact_InLogicExpr"})
		}

		verRet = ver.verify_specFact_when_given_orStmt_is_true(stmt, instantiatedLogicExprAsKnownSpecFact, knownFactUnderLogicExpr.Index, state)
		if verRet.IsErr() {
			return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{verRet.String()})
		}

		if verRet.IsTrue() {
			if state.WithMsg {
				return glob.NewVerMsg2(glob.StmtRetTypeTrue, stmt.String(), knownFactUnderLogicExpr.SpecFact.GetLine(), []string{knownFactUnderLogicExpr.UniFact.String()})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}
