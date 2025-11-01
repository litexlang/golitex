// Copyright 2024 Jiachen Shen.
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
	"strings"
)

func (ver *Verifier) specFactOrEqualFact_SpecMode(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	return ver.VerFactStmt(stmt, state.GetFinalRound()).ToBoolErr()
}

func (ver *Verifier) verSpecFact_BySpecMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
		if err != nil || ok {
			return BoolErrToVerRet(ok, err)
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verSpecFact_ByLogicMem(stmt *ast.SpecFactStmt, state *VerState) VerRet {
	nextState := state.GetAddRound()

	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_LogicMem(curEnv, stmt, nextState)
		if err != nil || ok {
			return BoolErrToVerRet(ok, err)
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verSpecFact_InSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_UniMem_atCurEnv(curEnv, stmt, state)
		if err != nil || ok {
			return ok, err
		}
	}
	return false, nil
}

func (ver *Verifier) verSpecFact_InLogicExpr_InUniFactMem(stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, state)
		if err != nil || ok {
			return ok, err
		}
	}

	return false, nil
}

func (ver *Verifier) specFact_inLogicExpr_inUniFactMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	nextState := state.GetAddRound().GetNoMsg()

	// return ver.iterate_KnownSpecInLogic_InUni_applyMatch(stmt, searchedSpecFactsInLogicExpr, nextState)
	return ver.iterate_KnownSpecInLogic_InUni_applyMatch_new(stmt, searchedSpecFactsInLogicExpr, nextState)
}

func (ver *Verifier) iterate_KnownSpecInLogic_InUni_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state *VerState) (bool, error) {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFactUnderLogicExpr := knownFacts[i]
		knownFact_paramProcessed := env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}

		ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, randomizedOrStmt, err := ver.preprocessUniFactParamsWithoutThenFacts_OrStmt(knownFactUnderLogicExpr.UniFact, knownFactUnderLogicExpr.LogicExpr)
		if err != nil {
			return false, err
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return false, err
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
				return false, fmt.Errorf(verRet.String())
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
		ok, err = ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		instantiatedLogicExpr, err := randomizedOrStmt.InstantiateFact(uniConMap)
		if err != nil {
			return false, err
		}
		instantiatedLogicExprAsKnownSpecFact, ok := instantiatedLogicExpr.(*ast.OrStmt)
		if !ok {
			return false, fmt.Errorf("instantiatedLogicExpr is not a KnownSpecFact_InLogicExpr")
		}

		ok, err = ver.verify_specFact_when_given_orStmt_is_true(stmt, instantiatedLogicExprAsKnownSpecFact, knownFactUnderLogicExpr.Index, state)
		if err != nil {
			return false, err
		}

		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), knownFactUnderLogicExpr.String())
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) specFact_UniMem_atCurEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if state == Round0NoMsg || state == Round0Msg {
		return false, fmt.Errorf("specFact_UniMem_atCurEnv: state is %s", state)
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	// return ver.iterate_KnownSpecInUniFacts_applyMatch(stmt, searchedSpecFacts, state)
	return ver.iterate_KnownSpecInUniFacts_applyMatch_new(stmt, searchedSpecFacts, state)
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]ast.Fc, state *VerState) (map[string]ast.Fc, bool, error) {
	newMap := map[string]ast.Fc{}
	for key, value := range paramArrMap {
		if len(value) == 1 {
			newMap[key] = value[0]
			continue
		}

		for i := 1; i < len(value); i++ {
			ok, err := ver.fcEqualSpec(value[0], value[i], state)
			if err != nil {
				return nil, false, err
			}
			if !ok {
				return nil, false, nil
			}
		}

		newMap[key] = value[0]
	}

	return newMap, true, nil
}

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	if len(knownFact.SpecFact.Params) != len(stmt.Params) {
		return false, nil
	}

	for i, knownParam := range knownFact.SpecFact.Params {
		ok, err := ver.verEqualBuiltin(knownParam, stmt.Params[i], state)
		if err != nil {
			return false, err
		}
		if !ok {
			ok, err := ver.fcEqualSpec(knownParam, stmt.Params[i], state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
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
			return verRet.ToBoolErr()
		}
	}

	if state.WithMsg {
		var verifiedBy strings.Builder
		verifiedBy.WriteString(knownFact.String())
		verifiedBy.WriteString("\n")
		for i, knownParam := range knownFact.SpecFact.Params {
			verifiedBy.WriteString(fmt.Sprintf("%s = %s\n", knownParam, stmt.Params[i]))
		}
		ver.successWithMsg(stmt.String(), verifiedBy.String())
	}

	return true, nil
}

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	return ver.iterateKnownSpecFacts_applyFcEqualSpec(stmt, knownFacts, state)
}

func (ver *Verifier) specFact_LogicMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactInLogicExprMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	if got {
		for _, knownFact := range knownFacts {
			ok, err := ver.useKnownOrFactToProveSpecFact(&knownFact, stmt, state)
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}
		}

	}

	return false, nil
}

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec(stmt *ast.SpecFactStmt, knownFacts []ast.SpecFactStmt, state *VerState) (bool, error) {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		ok, err := ver.matchTwoSpecFacts(stmt, &knownFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue LoopOverFacts
		}

		if state.WithMsg {
			ver.specFactSpecMemTrueMsg(stmt, knownFact)
		}

		return true, nil
	}

	return false, nil
}

func (ver *Verifier) matchTwoSpecFacts(stmt *ast.SpecFactStmt, knownFact *ast.SpecFactStmt, state *VerState) (bool, error) {
	if len(knownFact.Params) != len(stmt.Params) || knownFact.TypeEnum != stmt.TypeEnum {
		return false, nil
	}

	// 如果不区分 equal 和 其他事实的话，可能会出死循环
	if stmt.PropName == glob.KeySymbolEqual && stmt.IsTrue() {
		for i, knownParam := range knownFact.Params {
			ok, _, err := ver.cmpFc_Builtin_Then_Decompose_Spec(knownParam, stmt.Params[i], state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

	} else {
		newState := state.GetNoMsg()
		for i, knownParam := range knownFact.Params {
			ok, err := ver.fcEqualSpec(knownParam, stmt.Params[i], newState)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
	}

	return true, nil
}

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	ok, err := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	nextState := state.GetAddRound()
	for i, fact := range knownFact.LogicExpr.Facts {
		if i == knownFact.Index {
			continue
		}
		reversedFact := fact.ReverseTrue()
		// TODO: WARNING: 这里有问题，可能无限循环
		verRet := ver.VerFactStmt(reversedFact, nextState)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet.ToBoolErr()
		}
	}

	return true, nil
}

func (ver *Verifier) proveUniFactDomFacts(domFacts []ast.FactStmt, state *VerState) (bool, error) {
	if !state.isFinalRound() {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if ok {
				ok, err := ver.specFactOrEqualFact_SpecMode(asSpecFact, state)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
				}
			} else {
				verRet := ver.VerFactStmt(fact, state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet.ToBoolErr()
				}
			}
		}
		return true, nil
	} else {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if !ok {
				return false, nil
			}
			ok, err := ver.specFactOrEqualFact_SpecMode(asSpecFact, state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
		return true, nil
	}
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state *VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	// 其他是否都错
	for i := range orStmt.Facts {
		if i == index {
			continue
		}
		verRet := ver.VerFactStmt(orStmt.Facts[i].ReverseTrue(), state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet.ToBoolErr()
		}
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), orStmt.String())
	}

	return true, nil
}

func (ver *Verifier) iterate_KnownSpecInUniFacts_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state *VerState) (bool, error) {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFact_paramProcessed := knownFacts[i]
		// 这里需要用的是 instantiated 的 knownFact

		ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
		if err != nil {
			return false, err
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return false, err
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
				return false, err
			}
			if verRet.IsUnknown() {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		ok, err = ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, nextState)
		if err != nil {
			continue
		}

		if ok {
			if state.WithMsg {
				ver.successWithMsg(stmt.String(), knownFact_paramProcessed.UniFact.StringWithLine())
			}
			return true, nil
		}
	}

	return false, nil
}
