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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	"strconv"
	"strings"
)

func (ver *Verifier) specFactOrEqualFact_SpecMode(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	return ver.VerFactStmt(stmt, state.toFinalRound())
}

func (ver *Verifier) verSpecFact_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
		if err != nil || ok {
			return ok, err
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_ByLogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()

	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.specFact_LogicMem(curEnv, stmt, nextState)
		if err != nil || ok {
			return ok, err
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_InSpecFact_UniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) verSpecFact_InLogicExpr_InUniFactMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) specFact_inLogicExpr_inUniFactMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	nextState := state.addRound().toNoMsg()

	return ver.iterate_KnownSpecInLogic_InUni_applyMatch(stmt, searchedSpecFactsInLogicExpr, nextState)
}

func (ver *Verifier) iterate_KnownSpecInLogic_InUni_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state VerState) (bool, error) {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFactUnderLogicExpr := knownFacts[i]

		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 防止 两个不相等的参数对应到了同一个自由变量
		uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 如果有var没配对上，那就跳出循环
		if len(knownFactUnderLogicExpr.UniFact.Params) != len(uniConMap) {
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
			ok, err = ver.VerFactStmt(paramInParamSetFact, state)
			if err != nil {
				return false, err
			}
			if !ok {
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

		instantiatedLogicExpr, err := randomizedOrStmt.Instantiate(uniConMap)
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
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFactUnderLogicExpr.String())
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) specFact_UniMem_atCurEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state == Round0NoMsg || state == Round0Msg {
		return false, fmt.Errorf("specFact_UniMem_atCurEnv: state is %s", state)
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	return ver.iterate_KnownSpecInUniFacts_applyMatch(stmt, searchedSpecFacts, state)
}

func (ver *Verifier) iterate_KnownSpecInUniFacts_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state VerState) (bool, error) {
	for i := len(knownFacts) - 1; i >= 0; i-- {
		knownFact_paramProcessed := knownFacts[i]
		// 这里需要用的是 instantiated 的 knownFact

		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(knownFact_paramProcessed, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 防止 两个不相等的参数对应到了同一个自由变量
		uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 有一些 param 没有被实例化，则continue
		if len(knownFact_paramProcessed.UniFact.Params) != len(uniConMap) {
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

		// TODO 要证明在paramSet里
		paramInParamSetFacts := instantiatedUniFactWithoutThen.ParamInParamSetFacts(uniConMap)
		setFactSatisfied := true
		for _, paramInParamSetFact := range paramInParamSetFacts {
			ok, err = ver.VerFactStmt(paramInParamSetFact, state)
			if err != nil {
				return false, err
			}
			if !ok {
				setFactSatisfied = false
				break
			}
		}

		if !setFactSatisfied {
			continue
		}

		ok, err = ver.proveUniFactDomFacts(instantiatedUniFactWithoutThen.DomFacts, state)
		if err != nil {
			continue
		}

		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFact_paramProcessed.String())
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]ast.Fc, state VerState) (map[string]ast.Fc, bool, error) {
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

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
		ok, err := ver.VerFactStmt(fact.ReverseTrue(), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
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

// // 这里需要 recursive 地调用 这个，而不是只是 cmpFcRule. 之后再考虑recursive的情况
// func (ver *Verifier) fcEqualByBir(left ast.Fc, right ast.Fc, verState VerState) (bool, error) {
// 	var ok bool
// 	var msg string
// 	var err error

// 	defer func() {
// 		if ok {
// 			if verState.requireMsg() {
// 				ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), msg)
// 			}
// 		}
// 	}()

// 	ok, msg, err = cmp.Cmp_ByBIR(left, right)

// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	ok, msg, err = ver.verEqual_LeftToRightIsProj(left, right, true, verState)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	return false, nil
// }

func (ver *Verifier) verEqual_LeftIsTupleAtIndex(left, right ast.Fc, checkReverse bool, verState VerState) (bool, string, error) {
	if ast.IsFcFnWithHeadName(left, glob.TupleAtOp) {
		index, ok := left.(*ast.FcFn).Params[1].(ast.FcAtom)
		if !ok {
			return false, "", fmt.Errorf("index in %s is not a FcAtom", left)
		}
		indexAsInt, err := strconv.Atoi(string(index))
		if err != nil {
			return false, "", fmt.Errorf("index in %s is not a int", left)
		}
		if ast.IsFcFnWithHeadName(left.(*ast.FcFn).Params[0], glob.TupleFcFnHead) {
			if indexAsInt < 0 || indexAsInt >= len(left.(*ast.FcFn).Params[0].(*ast.FcFn).Params) {
				return false, "", fmt.Errorf("index in %s is out of range", left)
			}
			ok, err := ver.VerFactStmt(ast.NewEqualFact(left.(*ast.FcFn).Params[0].(*ast.FcFn).Params[indexAsInt], right), verState)
			if err != nil {
				return false, "", err
			}
			if ok {
				return true, "", nil
			}
		}
	}

	if checkReverse {
		return ver.verEqual_LeftIsTupleAtIndex(right, left, false, verState)
	} else {
		return false, "", nil
	}
}

func (ver *Verifier) isFnEqualFact_Check_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.NameIs(glob.KeySymbolEqualEqual) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("fn equal fact %s should have exactly two parameters, got: %d", stmt.String(), len(stmt.Params))
	}

	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), stmt.Params)
	if ok, err := ver.isEqualFact_Check(equalFact, state); err != nil {
		return false, err
	} else if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), equalFact.String())
		}
		return true, nil
	}

	leftFnDef, ok := ver.env.GetLatestFnTemplate(stmt.Params[0])
	if !ok {
		return false, nil
	}

	rightFnDef, ok := ver.env.GetLatestFnTemplate(stmt.Params[1])
	if !ok {
		return false, nil
	}

	// 元素数量相等
	if len(leftFnDef.Params) != len(rightFnDef.Params) {
		return false, nil
	}

	// left to right
	ok, err := ver.leftFnAlwaysEqualToRight(leftFnDef, rightFnDef, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// right to left
	ok, err = ver.leftFnAlwaysEqualToRight(rightFnDef, leftFnDef, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), "fn equal definition")
	}

	return true, nil
}

// TODO: 估计有点问题
func (ver *Verifier) leftFnAlwaysEqualToRight(leftFnDef *ast.FnTemplateStmt, rightFnDef *ast.FnTemplateStmt, state VerState) (bool, error) {
	panic("not implemented")
}

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	return ver.iterateKnownSpecFacts_applyFcEqualSpec(stmt, knownFacts, state)
}

func (ver *Verifier) specFact_LogicMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec(stmt *ast.SpecFactStmt, knownFacts []ast.SpecFactStmt, state VerState) (bool, error) {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		ok, err := ver.matchTwoSpecFacts(stmt, &knownFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue LoopOverFacts
		}

		if state.requireMsg() {
			ver.specFactSpecMemTrueMsg(stmt, knownFact)
		}

		return true, nil
	}

	return false, nil
}

func (ver *Verifier) matchTwoSpecFacts(stmt *ast.SpecFactStmt, knownFact *ast.SpecFactStmt, state VerState) (bool, error) {
	if len(knownFact.Params) != len(stmt.Params) || knownFact.TypeEnum != stmt.TypeEnum {
		return false, nil
	}

	for i, knownParam := range knownFact.Params {
		ok, err := ver.fcEqualSpec(knownParam, stmt.Params[i], state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	ok, err := ver.matchTwoSpecFacts(stmt, knownFact.SpecFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	nextState := state.addRound()
	for i, fact := range knownFact.LogicExpr.Facts {
		if i == knownFact.Index {
			continue
		}
		reversedFact := fact.ReverseTrue()
		// TODO: WARNING: 这里有问题，可能无限循环
		ok, err := ver.VerFactStmt(reversedFact, nextState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) proveUniFactDomFacts(domFacts []ast.FactStmt, state VerState) (bool, error) {
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
				ok, err := ver.VerFactStmt(fact, state)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
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

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	// 其他是否都错
	for i := range orStmt.Facts {
		if i == index {
			continue
		}
		ok, err := ver.VerFactStmt(orStmt.Facts[i].ReverseTrue(), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), orStmt.String())
	}

	return true, nil
}
