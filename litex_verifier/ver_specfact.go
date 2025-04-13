package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
)

func (ver *Verifier) SpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO 判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证？不过现在用 uniFact 后，真的还需要这个吗
	isPropProp, err := ver.IsPropProp(stmt, state)
	if err != nil {
		return false, err
	}
	if isPropProp {
		return ver.PropPropFact(stmt, state)
	}

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
			ver.successMsgEnd(fmt.Sprintf("%s = %s", stmt.Params[0], stmt.Params[1]), "")
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
			if stmt.IsTrue != knownFact.IsTrue {
				continue
			}

			ok, err := ver.FcSliceEqual(knownFact.Params, stmt.Params, state)

			if err != nil {
				return false, err
			}

			if ok {
				if state.requireMsg() {
					ver.successWithMsg(stmt.String(), knownFact.String(stmt.PropName))
				} else {
					ver.successNoMsg()
				}

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
		verified, err := ver.fcEqual(knownParam, right[i], specMode)
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
		reverseStmt = &ast.SpecFactStmt{IsTrue: stmt.IsTrue, PropName: stmt.PropName, Params: []ast.Fc{stmt.Params[1], stmt.Params[0]}}
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
			ok, err := ver.fcEqualSpec(value[0], value[i], state.addRound())
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
