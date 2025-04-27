// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	mem "golitex/litex_memory"
)

func (ver *Verifier) SpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
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

	// if stmt.IsEqualFact() {
	// 	ok, err := ver.fcEqual(stmt, state)
	// 	if err != nil {
	// 		return false, err
	// 	}
	// 	return ok, nil
	// }

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
	if stmt.IsEqualFact() {
		ok, err := ver.fcEqualSpec(stmt.Params[0], stmt.Params[1], state)
		if err != nil {
			return false, err
		}
		if state.requireMsg() && ok {
			ver.successMsgEnd(fmt.Sprintf("%s = %s", stmt.Params[0].String(), stmt.Params[1].String()), "")
		}
		return ok, err
	}

	ok, err := ver.btLogicOptBtRule(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNodeFacts, got := curEnv.SpecFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNodeFacts {
			if stmt.TypeEnum != knownFact.TypeEnum() {
				continue
			}

			if !knownFact.IsLogicExpr() {
				ok, err := ver.FcSliceEqual(knownFact.Params(), stmt.Params, state)

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
			} else {
				return ver.SpecFactSpecUnderLogicalExpr(&knownFact, stmt, state)
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
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
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
	searchedFacts, got := curEnv.CondFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

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

		verified, err := ver.FcSliceEqual(knownFact.Params, stmt.Params, Round0Msg)

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
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.SpecFactUniAtEnv(curEnv, stmt, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}

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
	searchedFacts, got := curEnv.UniFactMem.GetSpecFactNodeWithTheSameIsTrue(stmt)
	if !got {
		return false, nil
	}

	for _, knownFact := range searchedFacts {
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

		ok, err = ver.specFactUni(&knownFact, uniConMap, state)
		if err != nil {
			return false, err
		}

		if ok {
			ver.successWithMsg(stmt.String(), knownFact.String())
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

func (ver *Verifier) SpecFactSpecUnderLogicalExpr(knownFact *mem.StoredSpecFact, stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.FcSliceEqual(knownFact.Params(), stmt.Params, state)

	if err != nil {
		return false, err
	}

	currentLayerFact := knownFact.LogicExpr
	for _, factIndex := range knownFact.LogicExprIndexes {
		factAsLogicExpr, ok := currentLayerFact.Facts[factIndex].(*ast.LogicExprStmt)
		if !ok {
			return false, fmt.Errorf("logic expr stmt is not a logic expr stmt")
		}

		// 如果保存的是and，那and一定是全对的，不用验证
		if !factAsLogicExpr.IsOr {
			continue
		}

		// 如果是or，那只有在其他fact都验证失败的情况下，这个fact才算验证成功
		ok, err := ver.FactStmt(factAsLogicExpr, state.addRound().addRound())
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), knownFact.String())
		} else {
			ver.successNoMsg()
		}

		return true, nil
	}

	// TODO: 这里需要处理逻辑表达式
	return false, nil
}
