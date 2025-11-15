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

func (ver *Verifier) verSpecFact_BySpecMem(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.Env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		verRet := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verSpecFact_ByLogicMem(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	nextState := state.GetAddRound()

	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.Env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		verRet := ver.specFact_LogicMem(curEnv, stmt, nextState)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verSpecFact_InSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.Env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		verRet := ver.specFact_UniMem_atCurEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}
	return NewExecUnknown("")
}

func (ver *Verifier) verSpecFact_InLogicExpr_InUniFactMem(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.Env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		verRet := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) specFact_inLogicExpr_inUniFactMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return NewExecUnknown("")
	}

	nextState := state.GetAddRound().GetNoMsg()

	// return ver.iterate_KnownSpecInLogic_InUni_applyMatch(stmt, searchedSpecFactsInLogicExpr, nextState)
	return ver.iterate_KnownSpecInLogic_InUni_applyMatch_new(stmt, searchedSpecFactsInLogicExpr, nextState)
}

func (ver *Verifier) iterate_KnownSpecInLogic_InUni_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state *VerState) ExecRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFactUnderLogicExpr := knownFacts[i]
		knownFact_paramProcessed := env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}

		ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmt)
		if err != nil {
			return NewExecErr(err.Error())
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, randomizedOrStmt, err := ver.preprocessUniFactParamsWithoutThenFacts_OrStmt(knownFactUnderLogicExpr.UniFact, knownFactUnderLogicExpr.LogicExpr)
		if err != nil {
			return NewExecErr(err.Error())
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return NewExecErr(err.Error())
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
				return NewExecErr(verRet.String())
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
			return verRet
		}
		if verRet.IsUnknown() {
			continue
		}

		instantiatedLogicExpr, err := randomizedOrStmt.InstantiateFact(uniConMap)
		if err != nil {
			return NewExecErr(err.Error())
		}
		instantiatedLogicExprAsKnownSpecFact, ok := instantiatedLogicExpr.(*ast.OrStmt)
		if !ok {
			return NewExecErr("instantiatedLogicExpr is not a KnownSpecFact_InLogicExpr")
		}

		verRet = ver.verify_specFact_when_given_orStmt_is_true(stmt, instantiatedLogicExprAsKnownSpecFact, knownFactUnderLogicExpr.Index, state)
		if verRet.IsErr() {
			return verRet
		}

		if verRet.IsTrue() {
			execRet := NewExecTrue("")
			if state.WithMsg {
				execRet = ver.successWithMsg(stmt.String(), knownFactUnderLogicExpr.String(), execRet)
			}
			return execRet
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) specFact_UniMem_atCurEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if state == Round0NoMsg || state == Round0Msg {
		return NewExecErr(fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state))
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return NewExecUnknown("")
	}

	// return ver.iterate_KnownSpecInUniFacts_applyMatch(stmt, searchedSpecFacts, state)
	return BoolErrToExecRet(ver.iterate_KnownSpecInUniFacts_applyMatch_new(stmt, searchedSpecFacts, state).ToBoolErr())
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]ast.Obj, state *VerState) (map[string]ast.Obj, ExecRet) {
	newMap := map[string]ast.Obj{}
	for key, value := range paramArrMap {
		if len(value) == 1 {
			newMap[key] = value[0]
			continue
		}

		for i := 1; i < len(value); i++ {
			verRet := ver.fcEqualSpec(value[0], value[i], state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return nil, verRet
			}
		}

		newMap[key] = value[0]
	}

	return newMap, NewExecTrue("")
}

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(knownFact.SpecFact.Params) != len(stmt.Params) {
		return NewExecUnknown("")
	}

	for i, knownParam := range knownFact.SpecFact.Params {
		verRet := ver.verEqualBuiltin(knownParam, stmt.Params[i], state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			verRet := ver.fcEqualSpec(knownParam, stmt.Params[i], state)
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
		var verifiedBy strings.Builder
		verifiedBy.WriteString(knownFact.String())
		verifiedBy.WriteString("\n")
		for i, knownParam := range knownFact.SpecFact.Params {
			verifiedBy.WriteString(fmt.Sprintf("%s = %s\n", knownParam, stmt.Params[i]))
		}
		execRet := NewExecTrue("")
		execRet = ver.successWithMsg(stmt.String(), verifiedBy.String(), execRet)
		return execRet
	}

	return NewExecTrue("")
}

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return NewExecUnknown("")
	}

	return ver.iterateKnownSpecFacts_applyFcEqualSpec(stmt, knownFacts, state)
}

func (ver *Verifier) specFact_LogicMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactInLogicExprMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return NewExecUnknown("")
	}

	if got {
		for _, knownFact := range knownFacts {
			verRet := ver.useKnownOrFactToProveSpecFact(&knownFact, stmt, state)
			if verRet.IsErr() {
				return NewExecErr(verRet.String())
			}
			if verRet.IsTrue() {
				return NewExecTrue("")
			}
		}

	}

	return NewExecUnknown("")
}

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec(stmt *ast.SpecFactStmt, knownFacts []ast.SpecFactStmt, state *VerState) ExecRet {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.matchTwoSpecFacts(stmt, &knownFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}

		execRet := NewExecTrue("")
		if state.WithMsg {
			execRet = ver.specFactSpecMemTrueMsg(stmt, knownFact, execRet)
		}
		return execRet
	}

	return NewExecUnknown("")
}

func (ver *Verifier) matchTwoSpecFacts(stmt *ast.SpecFactStmt, knownFact *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(knownFact.Params) != len(stmt.Params) || knownFact.TypeEnum != stmt.TypeEnum {
		return NewExecUnknown("")
	}

	// 如果不区分 equal 和 其他事实的话，可能会出死循环
	if stmt.PropName == glob.KeySymbolEqual && stmt.IsTrue() {
		for i, knownParam := range knownFact.Params {
			verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(knownParam, stmt.Params[i], state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}

	} else {
		newState := state.GetNoMsg()
		for i, knownParam := range knownFact.Params {
			verRet := ver.fcEqualSpec(knownParam, stmt.Params[i], newState)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
	}

	return NewExecTrue("")
}

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	ver.newEnv(ver.Env)
	defer ver.deleteEnvAndRetainMsg()

	verRet := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
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
			return verRet
		}
	}

	return NewExecTrue("")
}

func (ver *Verifier) proveUniFactDomFacts(domFacts []ast.FactStmt, state *VerState) ExecRet {
	if !state.isFinalRound() {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if ok {
				verRet := BoolErrToExecRet(ver.VerFactStmt(asSpecFact, state.GetFinalRound()).ToBoolErr())
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
		return NewExecTrue("")
	} else {
		for _, fact := range domFacts {
			asSpecFact, ok := fact.(*ast.SpecFactStmt)
			if !ok {
				return NewExecUnknown("")
			}
			verRet := BoolErrToExecRet(ver.VerFactStmt(asSpecFact, state.GetFinalRound()).ToBoolErr())
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
		}
		return NewExecTrue("")
	}
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state *VerState) ExecRet {
	ver.newEnv(ver.Env)
	defer ver.deleteEnvAndRetainMsg()

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

	execRet := NewExecTrue("")
	if state.WithMsg {
		execRet = ver.successWithMsg(stmt.String(), orStmt.String(), execRet)
	}
	return execRet
}

func (ver *Verifier) iterate_KnownSpecInUniFacts_applyMatch_new(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state *VerState) ExecRet {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFact_paramProcessed := knownFacts[i]
		// 这里需要用的是 instantiated 的 knownFact

		ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(&knownFact_paramProcessed, stmt)
		if err != nil {
			return NewExecErr(err.Error())
		}
		if !ok {
			continue
		}

		randomizedUniFactWithoutThen, _, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownFact_paramProcessed.UniFact)
		if err != nil {
			return NewExecErr(err.Error())
		}

		for k, v := range uniConMap {
			if newParam, ok := paramMapStrToStr[k]; ok {
				uniConMap[newParam] = v
				delete(uniConMap, k)
			}
		}

		instantiatedUniFactWithoutThen, err := instantiateUniFactWithoutThenFacts(randomizedUniFactWithoutThen, uniConMap)
		if err != nil {
			return NewExecErr(err.Error())
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
				return NewExecErr(verRet.String())
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
			execRet := NewExecTrue("")
			if state.WithMsg {
				execRet = ver.successWithMsg(stmt.String(), knownFact_paramProcessed.UniFact.StringWithLine(), execRet)
			}
			return execRet
		}
	}

	return NewExecUnknown("")
}
