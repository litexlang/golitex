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
	cmp "golitex/cmp"
	env "golitex/environment"
	glob "golitex/glob"
	"strings"
)

func (ver *Verifier) specFactOrEqualFact_SpecMode(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	return ver.VerFactStmt(stmt, state.toFinalRound())
}

func (ver *Verifier) verSpecFact_BySpecMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	if ver.env.CurMatchProp == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	} else {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_MatchEnv_SpecMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_ByLogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	if ver.env.CurMatchProp == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_LogicMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	} else {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_LogicMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_MatchEnv_LogicMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	}

	return false, nil
}

// func (ver *Verifier) verSpecFact_SpecMem_LogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	ok, err := ver.verSpecFact_SpecMem(stmt, state)
// 	if err != nil || ok {
// 		return ok, err
// 	}

// 	ok, err = ver.verSpecFact_LogicMem(stmt, state)
// 	if err != nil || ok {
// 		return ok, err
// 	}

// 	return false, nil
// }

// func (ver *Verifier) verSpecFact_SpecMem_LogicMem_MatchEnv(stmt *ast.SpecFactStmt, state VerState) (bool, error) {

// upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

// 把这个判断放在 curEnv 的处理的外面（而不是每次迭代每次看），让整个程序快了30%
// if ver.env.CurMatchEnv == nil {
// 	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
// 		ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_LogicMem(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}
// 	}
// } else {
// 	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
// 		ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_LogicMem(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_MatchEnv(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}
// 	}
// }

// 	return false, nil
// }

func (ver *Verifier) verSpecFact_InSpecFact_UniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	if ver.env.CurMatchProp == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_UniMem_atCurEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}
		}
	} else {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_UniMem_atCurEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_MatchEnv_UniMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_InLogicExpr_InUniFactMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()
	upMostEnv := ver.todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	if ver.env.CurMatchProp == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}
		}
	} else {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_MatchEnv_InOrStmt_UniMem_atEnv(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	}

	return false, nil
}

func (ver *Verifier) specFact_MatchEnv_InOrStmt_UniMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	nextState := state.addRound().toNoMsg()

	return ver.iterate_KnownSpec_InLogic_InUni_MatchEnv_applyMatch(stmt, searchedSpecFactsInLogicExpr, nextState)
}

func (ver *Verifier) iterate_KnownSpec_InLogic_InUni_MatchEnv_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state VerState) (bool, error) {
	var previousSuppose *ast.SpecFactStmt = nil
	uniMapForMatchEnv := map[string]ast.Fc{}

	for _, knownFactUnderLogicExpr := range knownFacts {
		if knownFactUnderLogicExpr.EnvFact != previousSuppose {
			uniMapForMatchEnv = map[string]ast.Fc{}
			for i, param := range knownFactUnderLogicExpr.EnvFact.Params {
				atom, ok := param.(*ast.FcAtom)
				if !ok {
					return false, fmt.Errorf("known param %s is not an atom", param.String())
				}
				uniMapForMatchEnv[atom.Name] = ver.env.CurMatchProp.Params[i]
			}
			previousSuppose = knownFactUnderLogicExpr.EnvFact
		}

		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(env.KnownSpecFact_InUniFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 把 uniMapForMatchEnv 放入 paramArrMap
		for k, v := range uniMapForMatchEnv {
			// 如果不存在，那就新建；已经存在，就append
			if _, ok := paramArrMap[k]; !ok {
				paramArrMap[k] = []ast.Fc{v}
			} else {
				paramArrMap[k] = append(paramArrMap[k], v)
			}
		}

		// 防止 两个不相等的参数对应到了同一个自由变量
		uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		instantiatedLogicExpr, err := knownFactUnderLogicExpr.LogicExpr.Instantiate(uniConMap)
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
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}

// func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	ok, err := ver.verSpecFact_InSpecFact_UniMem(stmt, state)
// 	if err != nil || ok {
// 		return ok, err
// 	}

// 	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, state)

// nextState := state.addRound()
// upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

// if ver.env.CurMatchEnv == nil {
// 	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
// 		ok, err := ver.specFact_UniMem_asEnv(curEnv, stmt, nextState)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
// 		if err != nil || ok {
// 			return ok, err
// 		}
// 	}
// } else {
// 	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
// 		ok, err := ver.specFact_UniMem_asEnv(curEnv, stmt, nextState)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
// 		if err != nil || ok {
// 			return ok, err
// 		}

// 		ok, err = ver.specFact_MatchEnv_UniMem(curEnv, stmt, state)
// 		if err != nil || ok {
// 			return ok, err
// 		}
// 	}
// }

// return false, nil
// }

func (ver *Verifier) specFact_inLogicExpr_inUniFactMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedSpecFactsInLogicExpr, got := curEnv.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	nextState := state.addRound().toNoMsg()

	return ver.iterate_KnownSpecInLogic_InUni_applyMatch(stmt, searchedSpecFactsInLogicExpr, nextState)
}

func (ver *Verifier) iterate_KnownSpecInLogic_InUni_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.SpecFact_InLogicExpr_InUniFact, state VerState) (bool, error) {
	for _, knownFactUnderLogicExpr := range knownFacts {
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

		instantiatedLogicExpr, err := knownFactUnderLogicExpr.LogicExpr.Instantiate(uniConMap)
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
			} else {
				ver.successNoMsg()
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
	for _, knownFact := range knownFacts {
		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(knownFact, stmt)
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
		if len(knownFact.UniFact.Params) > len(uniConMap) {
			continue
		}

		insKnownUniFact, err := ast.InstantiateUniFact(knownFact.UniFact, uniConMap)
		if err != nil {
			return false, err
		}

		ok, err = ver.proveUniFactDomFacts(insKnownUniFact, state)
		if err != nil {
			return false, err
		}

		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFact.String())
			} else {
				ver.successNoMsg()
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
			// ok, err := ver.makeFcEqualFactAndVerify(value[0], value[i], state.addRound())
			// ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(value[0], value[i])
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
	// ok, err := ver.FcSliceEqual(knownFact.SpecFact.Params, stmt.Params, state)

	if len(knownFact.SpecFact.Params) != len(stmt.Params) {
		return false, nil
	}

	for i, knownParam := range knownFact.SpecFact.Params {
		ok, err := ver.fcEqual_Commutative_Associative_CmpRule(knownParam, stmt.Params[i], state)
		if err != nil {
			return false, err
		}
		if !ok {
			// ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(knownParam, stmt.Params[i])
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

	// ok, err := ver.verOrStmt(currentLayerFact, state)
	// if err != nil {
	// 	return false, err
	// }
	// if !ok {
	// 	return false, nil
	// }

	if state.requireMsg() {
		var verifiedBy strings.Builder
		verifiedBy.WriteString(knownFact.String())
		verifiedBy.WriteString("\n")
		for i, knownParam := range knownFact.SpecFact.Params {
			verifiedBy.WriteString(fmt.Sprintf("%s = %s\n", knownParam, stmt.Params[i]))
		}
		ver.successWithMsg(stmt.String(), verifiedBy.String())
	} else {
		ver.successNoMsg()
	}

	return true, nil
}

// 这里需要 recursive 地调用 这个，而不是只是 cmpFcRule. 之后再考虑recursive的情况
func (ver *Verifier) fcEqual_Commutative_Associative_CmpRule(left ast.Fc, right ast.Fc, verState VerState) (bool, error) {
	ok, msg, err := cmp.Cmp_ByBIR(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		if verState.requireMsg() {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left.String(), right.String()), msg)
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	// if left = opt(x,y) and opt is commutative, then left = opt(y,x)
	ok, err = ver.leftIsCommutativeAndUseCommutedLeftToCheckEqualRight(left, right, verState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.leftIsCommutativeAndUseCommutedLeftToCheckEqualRight(right, left, verState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.leftIsAssociative_UseAssociationToCheckEqual(left, right, verState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.leftIsAssociative_UseAssociationToCheckEqual(right, left, verState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) leftIsCommutativeAndUseCommutedLeftToCheckEqualRight(left ast.Fc, right ast.Fc, verState VerState) (bool, error) {
	if leftAsFn, ok := left.(*ast.FcFn); ok {
		if leftHeadAsAtom, ok := leftAsFn.FnHead.(*ast.FcAtom); ok {
			if ver.isCommutativeFn_BuiltinRule(*leftHeadAsAtom) { // 暂时认为只能是 atom 形式的opt name 才能判断
				if len(leftAsFn.Params) != 2 {
					return false, nil
				}

				commutativeLeft, ok := leftAsFn.HasTwoParamsAndSwitchOrder()
				if !ok {
					return false, nil
				}
				ok, msg, err := cmp.Cmp_ByBIR(commutativeLeft, right)
				// ok, err := ver.fcEqual(commutativeLeft, right, verState) // 死循环
				if err != nil {
					return false, err
				}
				if ok {
					if verState.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("%s = %s", left.String(), right.String()), fmt.Sprintf("%s is commutative, and %s", leftHeadAsAtom.String(), msg))
					} else {
						ver.successNoMsg()
					}
					return true, nil
				}
			}
		}
	}

	return false, nil
}

func (ver *Verifier) leftIsAssociative_UseAssociationToCheckEqual(left ast.Fc, right ast.Fc, verState VerState) (bool, error) {
	if leftAsFn, ok := left.(*ast.FcFn); ok {
		if leftHeadAsAtom, ok := leftAsFn.FnHead.(*ast.FcAtom); ok {
			if ver.isAssociativeFn_BuiltinRule(*leftHeadAsAtom) {
				leftAssociated, ok := leftAsFn.HasTwoParams_FirstParamHasTheSameNameAsItself()
				if !ok {
					return false, nil
				}

				ok, msg, err := cmp.Cmp_ByBIR(leftAssociated, right)
				if err != nil {
					return false, err
				}
				if ok {
					if verState.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("%s = %s", left.String(), right.String()), fmt.Sprintf("%s is associative, and %s", leftHeadAsAtom.String(), msg))
					} else {
						ver.successNoMsg()
					}
					return true, nil
				}
			}
		}
	}

	return false, nil
}

func (ver *Verifier) mathInductionFact_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if len(stmt.Params) != 1 {
		return false, fmt.Errorf("math induction fact %s should have exactly one parameter, got: %d", stmt.String(), len(stmt.Params))
	}

	propNameAsAtom, ok := stmt.Params[0].(*ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name as parameter, got: %s", stmt.String(), stmt.Params[0])
	}

	_, ok = ver.env.GetPropDef(*propNameAsAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name that is defined, got: %s", stmt.String(), propNameAsAtom)
	}

	// propName(0) is true
	propNameZeroFact := ast.NewSpecFactStmt(ast.TruePure, propNameAsAtom, []ast.Fc{ast.NewFcAtomWithName("0")})

	// propName(n) => propName(n+1)
	params := []string{"n"}

	domFacts := make([]ast.FactStmt, 1)
	domFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		propNameAsAtom,
		[]ast.Fc{ast.NewFcAtomWithName("n")},
	)
	thenFacts := make([]ast.FactStmt, 1)
	thenFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		propNameAsAtom,
		[]ast.Fc{ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolPlus), []ast.Fc{ast.NewFcAtomWithName("n"), ast.NewFcAtomWithName("1")})},
	)

	paramInSetsFacts := make([]ast.FactStmt, 1)
	paramInSetsFacts[0] = ast.NewInFact("n", ast.NewFcAtomWithName(glob.KeywordNatural))
	paramSets := make([]ast.Fc, 1)
	paramSets[0] = ast.NewFcAtomWithName(glob.KeywordNatural)

	nToNAddOneFact := ast.NewUniFact(
		params,
		paramSets,
		domFacts,
		thenFacts,
	)

	ok, err := ver.VerFactStmt(propNameZeroFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.VerFactStmt(nToNAddOneFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

// TODO: 没有测试过
// func (ver *Verifier) isSetEqualFact_Check_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	if !stmt.NameIs(glob.KeySymbolEqualEqualEqual) {
// 		return false, nil
// 	}

// 	if len(stmt.Params) != 2 {
// 		return false, fmt.Errorf("set equal fact %s should have exactly two parameters, got: %d", stmt.String(), len(stmt.Params))
// 	}

// 	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), stmt.Params)

// 	if ok, err := ver.isEqualFact_Check(equalFact, state); err != nil {
// 		return false, err
// 	} else if ok {
// 		if state.requireMsg() {
// 			ver.successWithMsg(stmt.String(), equalFact.String())
// 		} else {
// 			ver.successNoMsg()
// 		}
// 		return true, nil
// 	}

// 	leftSet := stmt.Params[0]
// 	rightSet := stmt.Params[1]

// 	// they are both sets
// 	// TODO: Currently can only check a fcAtom as set. If a set is a return value of a fn, current implementation will not work.
// 	ver.appendInternalWarningMsg("Currently can only check a fcAtom as set. If a set is a return value of a fn, current implementation will not work.")

// 	// _, ok := ver.env.GetSetDef(leftSet)

// 	var ok bool = false

// 	// 验证是否在set
// 	nextState := state.toFinalRound()
// 	ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{leftSet, ast.NewFcAtomWithName(glob.KeywordIn)}), nextState)
// 	if err != nil {
// 		return false, err
// 	}
// 	if !ok {
// 		return false, nil
// 	}

// 	if !ok {
// 		if state.requireMsg() {
// 			ver.successWithMsg(stmt.String(), fmt.Sprintf("left set %s is not a declared set", leftSet.String()))
// 		} else {
// 			ver.successNoMsg()
// 		}
// 		return false, nil
// 	}

// 	// 验证是否在set
// 	ok, err = ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeywordIn), []ast.Fc{rightSet, ast.NewFcAtomWithName(glob.KeywordIn)}), nextState)
// 	if err != nil {
// 		return false, err
// 	}
// 	if !ok {
// 		return false, nil
// 	}

// 	if !ok {
// 		if state.requireMsg() {
// 			ver.successWithMsg(stmt.String(), fmt.Sprintf("right set %s is not a declared set", rightSet.String()))
// 		} else {
// 			ver.successNoMsg()
// 		}
// 		return false, nil
// 	}

// 	paramInSetsFacts := make([]ast.FactStmt, 1)
// 	paramInSetsFacts[0] = ast.NewInFact("x", rightSet)
// 	paramSets := make([]ast.Fc, 1)
// 	paramSets[0] = rightSet

// 	uniFactItemsInLeftSetInRightSet := ast.NewUniFact(
// 		[]string{"x"},
// 		paramSets,
// 		[]ast.FactStmt{},
// 		[]ast.FactStmt{ast.NewInFact("x", rightSet)},
// 	)

// 	ok, err = ver.VerFactStmt(uniFactItemsInLeftSetInRightSet, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if !ok {
// 		return false, nil
// 	}

// 	paramInSetsFacts[0] = ast.NewInFact("x", leftSet)
// 	paramSets[0] = leftSet

// 	// forall x rightSet: x in leftSet
// 	uniFactItemsInRightSetInLeftSet := ast.NewUniFact(
// 		[]string{"x"},
// 		paramSets,
// 		[]ast.FactStmt{},
// 		[]ast.FactStmt{ast.NewInFact("x", leftSet)},
// 	)

// 	ok, err = ver.VerFactStmt(uniFactItemsInRightSetInLeftSet, state)
// 	if err != nil {
// 		return false, err
// 	}
// 	if !ok {
// 		return false, nil
// 	}

// 	if state.requireMsg() {
// 		ver.successWithMsg(stmt.String(), "set equal definition")
// 	} else {
// 		ver.successNoMsg()
// 	}

// 	return ok, nil
// }

func (ver *Verifier) isFnEqualFact_Check_BuiltinRules(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.NameIs(glob.KeySymbolEqualEqual) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("fn equal fact %s should have exactly two parameters, got: %d", stmt.String(), len(stmt.Params))
	}

	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.NewFcAtomWithName(glob.KeySymbolEqual), stmt.Params)
	if ok, err := ver.isEqualFact_Check(equalFact, state); err != nil {
		return false, err
	} else if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), equalFact.String())
		} else {
			ver.successNoMsg()
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
	} else {
		ver.successNoMsg()
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

		// return ver.iterateKnownLogicFacts_applyFcEqualSpec(stmt, knownFacts, state)
	}

	return false, nil
}

// TODO: 我不确定是不是用MatchEnv做cmp的时候，要不要修改compare的方式
// func (ver *Verifier) specFact_MatchEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	ok, err := ver.specFact_MatchEnv_SpecMem(curEnv, stmt, state)
// 	if err != nil || ok {
// 		return ok, err
// 	}

// 	ok, err = ver.specFact_MatchEnv_LogicMem(curEnv, stmt, state)
// 	if err != nil || ok {
// 		return ok, err
// 	}

// 	return false, nil
// }

func (ver *Verifier) specFact_MatchEnv_SpecMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// knownStruct, got := curEnv.KnownFactInMatchEnv.Get(ver.env.CurMatchProp.PropName.PkgName, ver.env.CurMatchProp.PropName.Name)
	knownStruct, got := curEnv.KnownFactInMatchEnv[ver.env.CurMatchProp.PropName.Name]

	if !got {
		return false, nil
	}

	knownFacts, got := knownStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)
	if !got {
		return false, nil
	}

	return ver.iterateKnownSpecFacts_applyFcEqualSpec_InMatchEnv(stmt, knownFacts, state)
}

func (ver *Verifier) specFact_MatchEnv_LogicMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// knownStruct, got := curEnv.KnownFactInMatchEnv.Get(ver.env.CurMatchProp.PropName.PkgName, ver.env.CurMatchProp.PropName.Name)
	knownStruct, got := curEnv.KnownFactInMatchEnv[ver.env.CurMatchProp.PropName.Name]

	if !got {
		return false, nil
	}

	knownFacts, got := knownStruct.SpecFactInLogicExprMem.GetSameEnumPkgPropFacts(stmt)
	if !got {
		return false, nil
	}

	return ver.iterateKnownLogicFacts_applyFcEqualSpec(stmt, knownFacts, state)
}

func (ver *Verifier) iterateKnownLogicFacts_applyFcEqualSpec(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InLogicExpr, state VerState) (bool, error) {
	for _, knownFactUnderLogicExpr := range knownFacts {
		ok, err := ver.SpecFactSpecUnderLogicalExpr(&knownFactUnderLogicExpr, stmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact, state VerState) (bool, error) {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		ok, err := ver.matchTwoSpecFacts(stmt, knownFact.Fact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue LoopOverFacts
		}

		if state.requireMsg() {
			ver.specFactSpecMemTrueMsg(stmt, knownFact)
		} else {
			ver.successNoMsg()
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

// TODO
func (ver *Verifier) specFact_MatchEnv_UniMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// knownStruct, got := curEnv.KnownFactInMatchEnv.Get(ver.env.CurMatchProp.PropName.PkgName, ver.env.CurMatchProp.PropName.Name)
	knownStruct, got := curEnv.KnownFactInMatchEnv[ver.env.CurMatchProp.PropName.Name]

	if !got {
		return false, nil
	}

	knownFacts, got := knownStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)
	if !got {
		return false, nil
	}

	return ver.iterate_KnownSpecInUniFacts_MatchEnv_applyMatch(stmt, knownFacts, state)
}

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec_InMatchEnv(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact, state VerState) (bool, error) {
	var previousSuppose *ast.SpecFactStmt = nil
	previousUniMap := map[string]ast.Fc{}

LoopOverFacts:
	for _, knownFact := range knownFacts {
		if len(knownFact.Fact.Params) != len(stmt.Params) || knownFact.Fact.TypeEnum != stmt.TypeEnum {
			continue
		}

		if knownFact.EnvFact != previousSuppose {
			previousUniMap = map[string]ast.Fc{}
			for i, param := range knownFact.EnvFact.Params {
				atom, ok := param.(*ast.FcAtom)
				if !ok {
					return false, fmt.Errorf("known param %s is not an atom", param.String())
				}
				previousUniMap[atom.Name] = ver.env.CurMatchProp.Params[i]
			}
			previousSuppose = knownFact.EnvFact
		}

		for i, knownParam := range knownFact.Fact.Params {
			knownParamInst, err := knownParam.Instantiate(previousUniMap)
			if err != nil {
				return false, err
			}

			ok, err := ver.fcEqualSpec(knownParamInst, stmt.Params[i], state)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		if state.requireMsg() {
			ver.newMsgEndWithCurMatchProp(stmt, knownFact, previousSuppose)
		} else {
			ver.successNoMsg()
		}

		return true, nil
	}
	return false, nil
}

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
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
		// panic("")
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

func (ver *Verifier) proveUniFactDomFacts(insUniFact *ast.UniFactStmt, state VerState) (bool, error) {
	if !state.isFinalRound() {
		for _, fact := range insUniFact.DomFacts {
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
		for _, fact := range insUniFact.DomFacts {
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

func (ver *Verifier) iterate_KnownSpecInUniFacts_MatchEnv_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniFact, state VerState) (bool, error) {
	var previousSuppose *ast.SpecFactStmt = nil
	uniMapForMatchEnv := map[string]ast.Fc{}

	for _, knownFact := range knownFacts {
		if knownFact.EnvFact != previousSuppose {
			uniMapForMatchEnv = map[string]ast.Fc{}
			for i, param := range knownFact.EnvFact.Params {
				atom, ok := param.(*ast.FcAtom)
				if !ok {
					return false, fmt.Errorf("known param %s is not an atom", param.String())
				}
				uniMapForMatchEnv[atom.Name] = ver.env.CurMatchProp.Params[i]
			}
			previousSuppose = knownFact.EnvFact
		}

		// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(knownFact, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		// 把 uniMapForMatchEnv 放入 paramArrMap
		for k, v := range uniMapForMatchEnv {
			// 如果不存在，那就新建；已经存在，就append
			if _, ok := paramArrMap[k]; !ok {
				paramArrMap[k] = []ast.Fc{v}
			} else {
				paramArrMap[k] = append(paramArrMap[k], v)
			}
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
		if len(knownFact.UniFact.Params) > len(uniConMap) {
			continue
		}

		insKnownUniFact, err := ast.InstantiateUniFact(knownFact.UniFact, uniConMap)
		if err != nil {
			return false, err
		}

		ok, err = ver.proveUniFactDomFacts(insKnownUniFact, state)
		if err != nil {
			return false, err
		}

		if ok {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFact.String())
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verify_specFact_when_given_orStmt_is_true(stmt *ast.SpecFactStmt, orStmt *ast.OrStmt, index int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
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
	} else {
		ver.successNoMsg()
	}

	return true, nil
}
