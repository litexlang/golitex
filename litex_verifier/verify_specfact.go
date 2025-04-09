package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
	"runtime"
)

func (ver *Verifier) SpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO 判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	isPropProp, err := ver.IsPropProp(stmt, state)
	if err != nil {
		return false, err
	}
	if isPropProp {
		return ver.PropPropFact(stmt, state)
	}

	// TODO 需要改成spec吗?
	nextState := state
	// nextState := state.addRound()

	ok, err := ver.SpecFactSpec(stmt, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// TODO 需要改成spec吗? 为了让下面这个能运行，我只能让nextState = state
	// prove:
	// know:
	//     when:
	//         forall x A:
	//             $p(x)
	//         then:
	//             $ForallXInAPX(2)
	// know:
	//     forall x A:
	//         $p(x)
	// $ForallXInAPX(2)

	// nextState := state.spec()
	nextState = state

	// 必须要spec一下，否则iff的时候，会永远循环下去。同时不能省略state，因为msg信息在里面
	// TODO 这里应该是 state 还是 uni 呢？？？
	ok, err = ver.SpecFactCond(stmt, nextState)
	// ok, err = ver.SpecFactCond(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	// TODO 这里应该是 state 还是 uni 呢？？？

	// TODO 需要改成spec吗? 为了下面这种情况，我必须让它是 spec()
	// prove:
	// know:
	//     forall x A:
	//         $p(x)
	//         then:
	//             $q(x)
	//     forall y A:
	//         $q(y)
	//         then:
	//             $p(y)
	// $q(1)
	// nextState = state.addRound()
	nextState = state

	// ok, err = ver.SpecFactUni(stmt, nextState)
	ok, err = ver.SpecFactUni(stmt, nextState)
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
		// ok, err := ver.FcEqual(stmt.Params[0], stmt.Params[1], state.noMsg())
		ok, err := ver.FcEqual(stmt.Params[0], stmt.Params[1], state)
		if err != nil {
			pc, _, _, _ := runtime.Caller(0)
			return false, glob.NewErrLinkAtFunc(err, runtime.FuncForPC(pc).Name(), "")
		}
		if state.requireMsg() && ok {
			ver.successMsgEnd(fmt.Sprintf("%s = %s", stmt.Params[0], stmt.Params[1]), "")
		}
		return ok, err
	}

	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		searchedNode, got := curEnv.SpecFactMem.GetNode(stmt)
		if !got {
			continue
		}

		for _, knownFact := range searchedNode.Facts {
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
	searched, got := curEnv.CondFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

LoopOverFacts:
	for _, knownFact := range searched.Facts {
		for _, f := range knownFact.Fact.CondFacts {
			// TODO 应该是 .spec() 吗？
			// ok, err := ver.FactStmt(f, state.spec())
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

	// nextState := state.spec()
	// TODO 这里应该取.spec() 吗?
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
	searched, got := curEnv.UniFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

	// uniConMap := map[string]ast.Fc{}
	for _, knownFact := range searched.Facts {
		// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
		paramArrMap, ok, err := ver.matchStoredUniConSpecFacts(knownFact, stmt)
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

		//! 把concrete parameter代入uniParam 对新的事实进行验证
		ok, err = ver.specFactUniWithUniConMap(&knownFact, uniConMap, state)
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

// 神奇的是，这个函数我不用传涉及到要验证的specFact，因为它的信息全在uniConMap里了，然后只要forall的cond全通过，就行
func (ver *Verifier) specFactUniWithUniConMap(knownStmt *mem.StoredUniSpecFact, uniConMap map[string]ast.Fc, state VerState) (bool, error) {
	ver.newEnv(uniConMap)
	defer ver.deleteEnvAndRetainMsg() // 万一condFact也有uniFact的检查,那就会改变env。我需要在此时能返回到原来的env

	// 传入的map必须能和所有的uniFact的param一一对应
	// e.g. 不等号传递性因此不能直接被使用，只能给传递性这个事实取个名字
	twoSlicesEqual := glob.SlicesEqualUnordered(glob.MapKeys(uniConMap), knownStmt.Fact.Params)
	if !twoSlicesEqual {
		return false, nil
	}

	for _, condFact := range knownStmt.Fact.DomFacts {
		// nextState := state.spec().noMsg()
		// TODO 这里应该取 spec 吗????
		nextState := state.addRound()
		ok, err := ver.FactStmt(condFact, nextState) // TODO: 这里最好要标注一下是specFact
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
