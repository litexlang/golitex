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
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	mem "golitex/litex_memory"
)

func (ver *Verifier) SpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.FcSatisfySpecFactParaReq(stmt)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if stmt.IsExistFact() {
		ok, err := ver.ExistPropFact(stmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	if stmt.IsExist_St_Fact() {
		ok, err := ver.Exist_St_PropFact(stmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return ver.pureSpecFact(stmt, state)
}

func (ver *Verifier) pureSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.SpecFactSpec(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.SpecFactCond(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	ok, err = ver.specFactProveByDefinition(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.SpecFactUni(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) SpecFactSpec(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsBuiltinLogicOpt() {
		return ver.btLogicOptSpec(stmt, state)
	}

	ok, err := ver.specFactUsingMemSpecifically(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) specFactUsingMemSpecifically(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		nodeNode, got := curEnv.SpecFactMem.GetNode(stmt)
		if !got {
			continue
		}
		searchedNodeFacts := nodeNode.Facts
		searchedNodeFactsUnderLogicExpr := nodeNode.FactsINLogicExpr

	LoopOverFacts:
		for _, knownFact := range searchedNodeFacts {
			// TODO: 我确实没想好是否要禁止用户让一个prop下面的fact有变长的参数列表
			if len(knownFact.Params()) != len(stmt.Params) {
				continue
			}

			for _, knownParam := range knownFact.Params() {
				ok, err := cmp.CmpFcRule(knownParam, stmt.Params[0])
				if err != nil {
					return false, err
				}
				if !ok {
					continue LoopOverFacts
				}
			}

			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFact.String())
			} else {
				ver.successNoMsg()
			}

			return true, nil
		}

		for _, knownFactUnderLogicExpr := range searchedNodeFactsUnderLogicExpr {
			ok, err := ver.SpecFactSpecUnderLogicalExpr(&knownFactUnderLogicExpr, stmt, state)
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

func (ver *Verifier) FcSliceEqual(left []ast.Fc, right []ast.Fc, specMode VerState) (bool, error) {
	if len(left) != len(right) {
		return false, fmt.Errorf("%v and %v have different length", left, right)
	}

	twoSpecFactHaveEqualParams := true
	for i, knownParam := range left {
		verified, err := ver.makeFcEqualFactAndVerify(knownParam, right[i], specMode)
		if err != nil {
			return false, err
		}
		if !verified {
			twoSpecFactHaveEqualParams = false
			break
		}
	}

	if twoSpecFactHaveEqualParams {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) SpecFactCond(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)
	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.SpecFactCondAtEnv(curEnv, stmt, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) SpecFactCondAtEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedNodeNode, got := curEnv.CondFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

	searchedFacts := searchedNodeNode.Facts

LoopOverFacts:
	for _, knownFact := range searchedFacts {
		for _, f := range knownFact.Fact.CondFacts {
			ok, err := ver.FactStmt(f, state)
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		verified, err := ver.FcSliceEqual(knownFact.SpecFact.Params, stmt.Params, Round0Msg)

		if err != nil {
			return false, err
		}

		if verified {
			if state.requireMsg() {
				ver.successWithMsg(stmt.String(), knownFact.Fact.String())
			} else {
				ver.successNoMsg()
			}
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) SpecFactUni(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// 处理可交换的prop
	isCom := ver.env.IsSpecFactPropCommutative(stmt)
	var reverseStmt *ast.SpecFactStmt = nil
	if isCom {
		reverseStmt = &ast.SpecFactStmt{TypeEnum: stmt.TypeEnum, PropName: stmt.PropName, Params: []ast.Fc{stmt.Params[1], stmt.Params[0]}}
	}

	nextState := state

	upMostEnv := theUpMostEnvWhereRelatedThingsAreDeclared(stmt)

	for curEnv := ver.env; curEnv != upMostEnv; curEnv = curEnv.Parent {
		ok, err := ver.SpecFactUniAtEnv(curEnv, stmt, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}

		// TODO 万一涉及到的prop名是变量，怎么办？

		// 处理可交换的prop
		if isCom {
			ok, err := ver.SpecFactUniAtEnv(curEnv, reverseStmt, nextState)
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

func (ver *Verifier) SpecFactUniAtEnv(curEnv *env.Env, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	searchedNodeNode, got := curEnv.UniFactMem.GetSpecFactNodeWithTheSameIsTrue(stmt)
	if !got {
		return false, nil
	}

	searchedSpecFacts := searchedNodeNode.Facts

	nextState := state.addRound().toNoMsg()

	for _, knownFact := range searchedSpecFacts {
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

		ok, err = ver.specFactUni(&knownFact, uniConMap, nextState)
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
			ok, err := ver.makeFcEqualFactAndVerify(value[0], value[i], state.addRound())
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

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *mem.StoredSpecFactInLogicExpr, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.FcSliceEqual(knownFact.Fact.Params, stmt.Params, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	currentLayerFact := knownFact.LogicExpr
	ok, err = ver.verifyLogicExprSteps(knownFact, currentLayerFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), knownFact.String())
	} else {
		ver.successNoMsg()
	}

	return true, nil
}

func (ver *Verifier) verifyLogicExprSteps(knownFact *mem.StoredSpecFactInLogicExpr, currentLayerFact *ast.LogicExprStmt, state VerState) (bool, error) {
	for i := 0; i < len(knownFact.Index)-1; i++ {
		factIndex := knownFact.Index[i]
		// 如果保存的是and，那and一定是全对的，不用验证
		if !currentLayerFact.IsOr {
			continue
		}

		// 如果是or，那只有在其他fact都验证失败的情况下，这个fact才算验证成功
		for i, fact := range currentLayerFact.Facts {
			if i == int(factIndex) {
				continue
			}

			// 需要reverse True
			ok, err := ver.FactStmt(fact.Reverse(), state.toSpec())
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}

		currentLayerFact = currentLayerFact.Facts[int(factIndex)].(*ast.LogicExprStmt)
	}

	// 处理最后一步
	factIndex := knownFact.Index[len(knownFact.Index)-1]
	if !currentLayerFact.IsOr {
		return true, nil
	}

	for i, fact := range currentLayerFact.Facts {
		if i == int(factIndex) {
			continue
		}

		ok, err := ver.FactStmt(fact.Reverse(), state.addRound().addRound())
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) specFactProveByDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	nextState := state.toSpec()

	defStmt, ok := ver.env.GetPropDef(stmt.PropName)
	if !ok {
		return false, nil
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Fc{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := iffToProp.Instantiate(paramArrMap)
	if err != nil {
		return false, err
	}
	insIffToPropAsUniFact, ok := instantiatedIffToProp.(*ast.ConUniFactStmt)
	if !ok {
		return false, fmt.Errorf("instantiatedIffToProp is not a ConUniFactStmt")
	}

	// prove all domFacts are true
	for _, domFact := range insIffToPropAsUniFact.DomFacts {
		ok, err := ver.FactStmt(domFact, nextState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), defStmt.String())
	} else {
		ver.successNoMsg()
	}

	return true, nil
}
