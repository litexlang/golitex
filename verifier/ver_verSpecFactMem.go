// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

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
	return ver.FactStmt(stmt, state.toFnialRound())
}

func (ver *Verifier) verSpecFact_SpecMem_LogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	// 把这个判断放在 curEnv 的处理的外面（而不是每次迭代每次看），让整个程序快了30%
	if ver.env.CurMatchEnv == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_SpecMem_atEnv(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_LogicMem(curEnv, stmt, state)
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

			ok, err = ver.specFact_LogicMem(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_MatchEnv(curEnv, stmt, state)
			if err != nil || ok {
				return ok, err
			}
		}
	}

	return false, nil
}

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()

	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	if ver.env.CurMatchEnv == nil {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_UniMem_asEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}
		}
	} else {
		for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
			ok, err := ver.specFact_UniMem_asEnv(curEnv, stmt, nextState)
			if err != nil || ok {
				return ok, err
			}

			ok, err = ver.specFact_inLogicExpr_inUniFactMem_atEnv(curEnv, stmt, nextState)
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
		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec(env.KnownSpecFact_InUniSpecFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}, stmt)
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

		instaniatedLogicExpr, err := knownFactUnderLogicExpr.LogicExpr.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		instaniatedLogicExprAsKnownSpecFact, ok := instaniatedLogicExpr.(*ast.OrStmt)
		if !ok {
			return false, fmt.Errorf("instaniatedLogicExpr is not a KnownSpecFact_InLogicExpr")
		}

		knownSpecFact_InLogicExpr_InUniFact := env.KnownSpecFact_InLogicExpr{
			SpecFact: stmt,
			// Index:     knownFactUnderLogicExpr.Index,
			LogicExpr: instaniatedLogicExprAsKnownSpecFact,
		}

		ok, err = ver.SpecFactSpecUnderLogicalExpr(&knownSpecFact_InLogicExpr_InUniFact, stmt, state)
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

func (ver *Verifier) specFact_UniMem_asEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	nextState := state.addRound()

	return ver.iterate_KnownSpecInUniFacts_applyMatch(stmt, searchedSpecFacts, nextState)
}

func (ver *Verifier) iterate_KnownSpecInUniFacts_applyMatch(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact_InUniSpecFact, state VerState) (bool, error) {
	for _, knownFact := range knownFacts {
		// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
		paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec(knownFact, stmt)
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

// func (ver *Verifier) SpecFactUniAtEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	nextState := state.addRound().toNoMsg()

// 	searchedSpecFacts, got := curEnv.KnownFacts.SpecFactInUniFactMem.GetSameEnumPkgPropFacts(stmt)
// 	if got {
// 		for _, knownFact := range searchedSpecFacts {
// 			// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
// 			paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec(knownFact, stmt)
// 			if err != nil {
// 				return false, err
// 			}
// 			if !ok {
// 				continue
// 			}

// 			// 防止 两个不相等的参数对应到了同一个自由变量
// 			uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
// 			if err != nil {
// 				return false, err
// 			}
// 			if !ok {
// 				continue
// 			}

// 			insKnownUniFact, err := ast.InstantiateUniFact(knownFact.UniFact, uniConMap)
// 			if err != nil {
// 				return false, err
// 			}

// 			ok, err = ver.proveUniFactDomFacts(insKnownUniFact, state)
// 			if err != nil {
// 				return false, err
// 			}

// 			// ok, err = ver.specFactUni(&knownFact, uniConMap, nextState)
// 			// if err != nil {
// 			// 	return false, err
// 			// }

// 			if ok {
// 				if state.requireMsg() {
// 					ver.successWithMsg(stmt.String(), knownFact.String())
// 				} else {
// 					ver.successNoMsg()
// 				}
// 				return true, nil
// 			}
// 		}
// 	}

// 	searchedSpecFactsInLogicExpr, got := curEnv.KnownFacts.SpecFact_InLogicExpr_InUniFactMem.GetSameEnumPkgPropFacts(stmt)
// 	if got {
// 		for _, knownFactUnderLogicExpr := range searchedSpecFactsInLogicExpr {
// 			paramArrMap, ok, err := ver.matchStoredUniSpecWithSpec(env.KnownSpecFact_InUniSpecFact{SpecFact: knownFactUnderLogicExpr.SpecFact, UniFact: knownFactUnderLogicExpr.UniFact}, stmt)
// 			if err != nil {
// 				return false, err
// 			}
// 			if !ok {
// 				continue
// 			}

// 			// 防止 两个不相等的参数对应到了同一个自由变量
// 			uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
// 			if err != nil {
// 				return false, err
// 			}
// 			if !ok {
// 				continue
// 			}

// 			instaniatedLogicExpr, err := knownFactUnderLogicExpr.LogicExpr.Instantiate(uniConMap)
// 			if err != nil {
// 				return false, err
// 			}
// 			instaniatedLogicExprAsKnownSpecFact, ok := instaniatedLogicExpr.(*ast.LogicExprStmt)
// 			if !ok {
// 				return false, fmt.Errorf("instaniatedLogicExpr is not a KnownSpecFact_InLogicExpr")
// 			}

// 			knownSpecFact_InLogicExpr_InUniFact := env.KnownSpecFact_InLogicExpr{
// 				SpecFact:  stmt,
// 				Index:     knownFactUnderLogicExpr.Index,
// 				LogicExpr: instaniatedLogicExprAsKnownSpecFact,
// 			}

// 			ok, err = ver.SpecFactSpecUnderLogicalExpr(&knownSpecFact_InLogicExpr_InUniFact, stmt, nextState)
// 			if err != nil {
// 				return false, err
// 			}

// 			if ok {
// 				if state.requireMsg() {
// 					ver.successWithMsg(stmt.String(), knownFactUnderLogicExpr.String())
// 				} else {
// 					ver.successNoMsg()
// 				}
// 				return true, nil
// 			}
// 		}
// 	}

// 	return false, nil
// }

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
	ok, err := ver.verOrStmt(currentLayerFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

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

// func (ver *Verifier) verifyLogicExprSteps(knownFact *env.KnownSpecFact_InLogicExpr, currentLayerFact *ast.LogicExprStmt, state VerState) (bool, error) {
// 	for i := 0; i < len(knownFact.Index)-1; i++ {
// 		factIndex := knownFact.Index[i]
// 		// 如果保存的是and，那and一定是全对的，不用验证
// 		if !currentLayerFact.IsOr {
// 			continue
// 		}

// 		// 如果是or，那只有在其他fact都验证失败的情况下，这个fact才算验证成功
// 		for i, fact := range currentLayerFact.Facts {
// 			if i == int(factIndex) {
// 				continue
// 			}

// 			// 需要reverse True
// 			ok, err := ver.FactStmt(fact.ReverseIsTrue(), state.toFnialRound())
// 			if err != nil {
// 				return false, err
// 			}
// 			if !ok {
// 				return false, nil
// 			}
// 		}

// 		currentLayerFact = currentLayerFact.Facts[int(factIndex)].(*ast.LogicExprStmt)
// 	}

// 	// 处理最后一步
// 	factIndex := knownFact.Index[len(knownFact.Index)-1]
// 	if !currentLayerFact.IsOr {
// 		return true, nil
// 	}

// 	for i, fact := range currentLayerFact.Facts {
// 		if i == int(factIndex) {
// 			continue
// 		}

// 		ok, err := ver.FactStmt(fact.ReverseIsTrue(), state.addRound().addRound())
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, nil
// 		}
// 	}

// 	return true, nil
// }

// func (ver *Verifier) specFactProveByDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	nextState := state.addRound()

// 	if !stmt.IsTrue() {
// 		return false, nil
// 	}

// 	defStmt, ok := ver.env.GetPropDef(stmt.PropName)
// 	if !ok {
// 		// 这里可能是因为这个propName是exist prop，所以没有定义
// 		return false, nil
// 	}

// 	if len(defStmt.IffFacts) == 0 {
// 		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
// 		return false, nil
// 	}

// 	iffToProp := defStmt.IffToPropUniFact()
// 	paramArrMap := map[string]ast.Fc{}
// 	for i, param := range stmt.Params {
// 		paramArrMap[defStmt.DefHeader.Params[i]] = param
// 	}

// 	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
// 	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
// 	if err != nil {
// 		return false, err
// 	}
// 	// prove all domFacts are true
// 	for _, domFact := range instantiatedIffToProp.DomFacts {
// 		ok, err := ver.FactStmt(domFact, nextState)
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			return false, nil
// 		}
// 	}

// 	if state.requireMsg() {
// 		ver.successWithMsg(stmt.String(), defStmt.String())
// 	} else {
// 		ver.successNoMsg()
// 	}

// 	return true, nil
// }

// 这里需要 recursive 地调用 这个，而不是只是 cmpFcRule. 之后再考虑recursive的情况
func (ver *Verifier) fcEqual_Commutative_Associative_CmpRule(left ast.Fc, right ast.Fc, verState VerState) (bool, error) {
	ok, err := cmp.CmpFcRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
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
			if ver.isCommutativeFn(*leftHeadAsAtom) { // 暂时认为只能是 atom 形式的opt name 才能判断
				if len(leftAsFn.ParamSegs) != 2 {
					return false, nil
				}

				commutativeLeft, ok := leftAsFn.HasTwoParamsAndSwitchOrder()
				if !ok {
					return false, nil
				}
				ok, err := cmp.CmpFcRule(commutativeLeft, right)
				// ok, err := ver.fcEqual(commutativeLeft, right, verState) // 死循环
				if err != nil {
					return false, err
				}
				if ok {
					if verState.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("%s = %s", left.String(), right.String()), fmt.Sprintf("%s is commutative", leftHeadAsAtom.String()))
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
			if ver.isAssociativeFn(*leftHeadAsAtom) {
				leftAssociated, ok := leftAsFn.HasTwoParams_FirstParamHasTheSameNameAsItself()
				if !ok {
					return false, nil
				}

				ok, err := cmp.CmpFcRule(leftAssociated, right)
				if err != nil {
					return false, err
				}
				if ok {
					if verState.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("%s = %s", left.String(), right.String()), fmt.Sprintf("%s is associative", leftHeadAsAtom.String()))
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

func (ver *Verifier) mathInductionFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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
	propNameZeroFact := ast.NewSpecFactStmt(ast.TruePure, *propNameAsAtom, []ast.Fc{ast.NewFcAtomWithName("0")})

	// propName(n) => propName(n+1)
	params := []string{fmt.Sprintf("%sn", glob.UniParamPrefix)}
	domFacts := make([]ast.FactStmt, 1)
	domFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		*propNameAsAtom,
		[]ast.Fc{ast.NewFcAtomWithName(fmt.Sprintf("%sn", glob.UniParamPrefix))},
	)
	thenFacts := make([]ast.FactStmt, 1)
	thenFacts[0] = ast.NewSpecFactStmt(
		ast.TruePure,
		*propNameAsAtom,
		[]ast.Fc{ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolPlus), []ast.Fc{ast.NewFcAtomWithName(fmt.Sprintf("%sn", glob.UniParamPrefix)), ast.NewFcAtomWithName("1")})},
	)

	paramInSetsFacts := make([]ast.FactStmt, 1)
	paramInSetsFacts[0] = ast.Param_ParamSet_ToInFact(fmt.Sprintf("%sn", glob.UniParamPrefix), ast.NewFcAtomWithName(glob.KeywordNatural))

	nToNAddOneFact := ast.NewUniFactStmtWithSetReqInDom(
		params,
		domFacts,
		thenFacts,
		ast.EmptyIffFacts,
		paramInSetsFacts,
	)

	ok, err := ver.FactStmt(propNameZeroFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.FactStmt(nToNAddOneFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

// TODO: 没有测试过
func (ver *Verifier) isSetEqualFact_Check(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.NameIs(glob.KeySymbolEqualEqualEqual) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("set equal fact %s should have exactly two parameters, got: %d", stmt.String(), len(stmt.Params))
	}

	equalFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), stmt.Params)

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

	leftSet := stmt.Params[0]
	rightSet := stmt.Params[1]

	// they are both sets
	// TODO: Currently can only check a fcAtom as set. If a set is a return value of a fn, current implementation will not work.
	ver.appendInternalWarningMsg("Currently can only check a fcAtom as set. If a set is a return value of a fn, current implementation will not work.")
	_, ok := ver.env.GetSetDef(leftSet)
	if !ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("left set %s is not a declared set", leftSet.String()))
		} else {
			ver.successNoMsg()
		}
		return false, nil
	}
	_, ok = ver.env.GetSetDef(rightSet)
	if !ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), fmt.Sprintf("right set %s is not a declared set", rightSet.String()))
		} else {
			ver.successNoMsg()
		}
		return false, nil
	}

	paramInSetsFacts := make([]ast.FactStmt, 1)
	paramInSetsFacts[0] = ast.Param_ParamSet_ToInFact(fmt.Sprintf("%sx", glob.UniParamPrefix), rightSet)

	// use newfunction
	uniFactItemsInLeftSetInRightSet := ast.NewUniFactStmtWithSetReqInDom(
		[]string{fmt.Sprintf("%sx", glob.UniParamPrefix)},
		[]ast.FactStmt{},
		[]ast.FactStmt{ast.Param_ParamSet_ToInFact(fmt.Sprintf("%sx", glob.UniParamPrefix), rightSet)},
		ast.EmptyIffFacts,
		paramInSetsFacts,
	)

	ok, err := ver.FactStmt(uniFactItemsInLeftSetInRightSet, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	paramInSetsFacts[0] = ast.Param_ParamSet_ToInFact(fmt.Sprintf("%sx", glob.UniParamPrefix), leftSet)
	// forall x rightSet: x in leftSet
	uniFactItemsInRightSetInLeftSet := ast.NewUniFactStmtWithSetReqInDom(
		[]string{fmt.Sprintf("%sx", glob.UniParamPrefix)},
		[]ast.FactStmt{},
		[]ast.FactStmt{ast.Param_ParamSet_ToInFact(fmt.Sprintf("%sx", glob.UniParamPrefix), leftSet)},
		ast.EmptyIffFacts,
		paramInSetsFacts,
	)

	ok, err = ver.FactStmt(uniFactItemsInRightSetInLeftSet, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), "set equal definition")
	} else {
		ver.successNoMsg()
	}

	return ok, nil
}

func (ver *Verifier) isFnEqualFact_Check(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.NameIs(glob.KeySymbolEqualEqual) {
		return false, nil
	}

	if len(stmt.Params) != 2 {
		return false, fmt.Errorf("fn equal fact %s should have exactly two parameters, got: %d", stmt.String(), len(stmt.Params))
	}

	equalFact := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), stmt.Params)
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

	leftFnDef, ok := ver.env.GetFnDef(stmt.Params[0])
	if !ok {
		return false, nil
	}

	rightFnDef, ok := ver.env.GetFnDef(stmt.Params[1])
	if !ok {
		return false, nil
	}

	// 元素数量相等
	if len(leftFnDef.DefHeader.Params) != len(rightFnDef.DefHeader.Params) {
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
func (ver *Verifier) leftFnAlwaysEqualToRight(leftFnDef *ast.DefFnStmt, rightFnDef *ast.DefFnStmt, state VerState) (bool, error) {
	// 函数相等，意味着定义域相等，每个元素上的返回值相等
	// 定义域相等

	// left to right
	uniMap_RightParamAsKey_LeftParamAsValue := map[string]ast.Fc{}
	leftParamAsFcs := []ast.Fc{}
	rightParamAsFcs := []ast.Fc{}
	for i, rightParam := range rightFnDef.DefHeader.Params {
		ithLeftParamAsAtom := ast.NewFcAtomWithName(leftFnDef.DefHeader.Params[i])
		uniMap_RightParamAsKey_LeftParamAsValue[rightParam] = ithLeftParamAsAtom
		leftParamAsFcs = append(leftParamAsFcs, ithLeftParamAsAtom)
		rightParamAsFcs = append(rightParamAsFcs, ast.NewFcAtomWithName(rightParam))
	}

	leftToRightDom := []ast.FactStmt{}
	leftToRightDom = append(leftToRightDom, leftFnDef.DefHeader.ParamInSetsFacts...)
	leftToRightDom = append(leftToRightDom, leftFnDef.DomFacts...)

	leftToRightThenFacts := []ast.FactStmt{}
	leftToRightThenFacts = append(leftToRightThenFacts, rightFnDef.DefHeader.ParamInSetsFacts...)

	// dom 里的东西对应上
	for _, rightDomFact := range rightFnDef.DomFacts {
		instRightDomFact, err := rightDomFact.Instantiate(uniMap_RightParamAsKey_LeftParamAsValue)
		if err != nil {
			return false, err
		}
		leftToRightThenFacts = append(leftToRightThenFacts, instRightDomFact)
	}

	// 返回值类型一样

	leftToRight := ast.NewUniFactStmtWithSetReqInDom(
		leftFnDef.DefHeader.Params,
		leftToRightDom,
		leftToRightThenFacts,
		ast.EmptyIffFacts,
		leftFnDef.DefHeader.ParamInSetsFacts,
	)

	ok, err := ver.FactStmt(leftToRight, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	// 返回值时刻相等
	leftFnNameAsSpecFact := ast.NewFcFn(
		ast.NewFcAtomWithName(leftFnDef.DefHeader.Name),
		leftParamAsFcs,
	)

	rightFnNameAsSpecFact := ast.NewFcFn(
		ast.NewFcAtomWithName(rightFnDef.DefHeader.Name),
		rightParamAsFcs,
	)

	leftEqualRight := ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{leftFnNameAsSpecFact, rightFnNameAsSpecFact})

	leftFnAlwaysEqualRightFn := ast.NewUniFactStmtWithSetReqInDom(
		leftFnDef.DefHeader.Params,
		leftToRightDom,
		[]ast.FactStmt{leftEqualRight},
		ast.EmptyIffFacts,
		leftFnDef.DefHeader.ParamInSetsFacts,
	)

	ok, err = ver.FactStmt(leftFnAlwaysEqualRightFn, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) specFact_SpecMem_atEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(stmt)

	if !got {
		return false, nil
	}

	return ver.iterateKnownSpecFacts_applyFcEqualSpec(stmt, knownFacts, state)
}

func (ver *Verifier) specFactSpecMemTrueMsg(stmt *ast.SpecFactStmt, knownFact env.KnownSpecFact) {
	var verifiedBy strings.Builder
	verifiedBy.WriteString(knownFact.String())
	verifiedBy.WriteString("\n")
	for i, knownParam := range knownFact.Fact.Params {
		verifiedBy.WriteString(fmt.Sprintf("%s = %s\n", knownParam, stmt.Params[i]))
	}
	ver.successWithMsg(stmt.String(), verifiedBy.String())
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
func (ver *Verifier) specFact_MatchEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.specFact_MatchEnv_SpecMem(curEnv, stmt, state)
	if err != nil || ok {
		return ok, err
	}

	ok, err = ver.specFact_MatchEnv_LogicMem(curEnv, stmt, state)
	if err != nil || ok {
		return ok, err
	}

	return false, nil
}

func (ver *Verifier) specFact_MatchEnv_SpecMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	knownStruct, got := curEnv.KnownFactInMatchEnv.Get(ver.env.CurMatchEnv.Fact.PropName.PkgName, ver.env.CurMatchEnv.Fact.PropName.Name)

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
	knownStruct, got := curEnv.KnownFactInMatchEnv.Get(ver.env.CurMatchEnv.Fact.PropName.PkgName, ver.env.CurMatchEnv.Fact.PropName.Name)

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
		if len(knownFact.Fact.Params) != len(stmt.Params) || knownFact.Fact.TypeEnum != stmt.TypeEnum {
			continue
		}

		for i, knownParam := range knownFact.Fact.Params {
			ok, err := ver.fcEqualSpec(knownParam, stmt.Params[i], state)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
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

// TODO
func (ver *Verifier) specFact_MatchEnv_UniMem(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	_ = curEnv
	_ = stmt
	_ = state
	return false, nil
}

func (ver *Verifier) iterateKnownSpecFacts_applyFcEqualSpec_InMatchEnv(stmt *ast.SpecFactStmt, knownFacts []env.KnownSpecFact, state VerState) (bool, error) {
	var previousSuppose *ast.SupposePropMatchStmt = nil
	previousUniMap := map[string]ast.Fc{}

LoopOverFacts:
	for _, knownFact := range knownFacts {
		if len(knownFact.Fact.Params) != len(stmt.Params) || knownFact.Fact.TypeEnum != stmt.TypeEnum {
			continue
		}

		if knownFact.EnvFact != previousSuppose {
			for i, param := range knownFact.Fact.Params {
				atom, ok := param.(*ast.FcAtom)
				if !ok {
					return false, fmt.Errorf("known param %s is not an atom", param.String())
				}
				previousUniMap[atom.Name] = stmt.Params[i]
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
			ver.specFactSpecMemTrueMsg(stmt, knownFact)
		} else {
			ver.successNoMsg()
		}

		return true, nil
	}
	return false, nil
}

func (ver *Verifier) useKnownOrFactToProveSpecFact(knownFact *env.KnownSpecFact_InLogicExpr, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchEnv)
	defer ver.deleteEnvAndRetainMsg()

	// TODO 要让 stmt 和 第index位的事实match上
	_ = stmt

	for i, fact := range knownFact.LogicExpr.Facts {
		if i == knownFact.Index {
			continue
		}
		reversedFact := fact.ReverseSpecFact()
		// panic("")
		// TODO: WARNING: 这里有问题，可能无限循环
		ok, err := ver.FactStmt(reversedFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
