package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
	parser "golitex/litex_parser"
	"runtime"
)

func (ver *Verifier) SpecFact(stmt *parser.SpecFactStmt, state VerState) (bool, error) {
	// TODO 判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	isPropProp, err := ver.IsPropProp(stmt, state)
	if err != nil {
		return false, err
	}
	if isPropProp {
		return ver.PropPropFact(stmt, state)
	}

	nextState := state.spec()

	ok, err := ver.SpecFactSpec(stmt, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	// 必须要spec一下，否则iff的时候，会永远循环下去。同时不能省略state，因为msg信息在里面
	ok, err = ver.SpecFactCond(stmt, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = ver.SpecFactUni(stmt, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) SpecFactSpec(stmt *parser.SpecFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) SpecFactCond(stmt *parser.SpecFactStmt, state VerState) (bool, error) {
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

func (ver *Verifier) SpecFactCondAtEnv(curEnv *env.Env, stmt *parser.SpecFactStmt, state VerState) (bool, error) {
	searched, got := curEnv.CondFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

LoopOverFacts:
	for _, knownFact := range searched.Facts {
		for _, f := range knownFact.Fact.CondFacts {
			ok, err := ver.FactStmt(f, state.spec())
			if err != nil {
				return false, err
			}
			if !ok {
				continue LoopOverFacts
			}
		}

		verified, err := ver.FcSliceEqual(knownFact.Params, stmt.Params, AnyMsg)

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

func (ver *Verifier) SpecFactUni(stmt *parser.SpecFactStmt, state VerState) (bool, error) {
	// 处理可交换的prop
	isCom := ver.env.IsSpecFactPropCommutative(stmt)
	var reverseStmt *parser.SpecFactStmt = nil
	if isCom {
		reverseStmt = &parser.SpecFactStmt{IsTrue: stmt.IsTrue, PropName: stmt.PropName, Params: []parser.Fc{stmt.Params[1], stmt.Params[0]}}
	}

	nextState := state.spec()
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

func (ver *Verifier) SpecFactUniAtEnv(curEnv *env.Env, stmt *parser.SpecFactStmt, state VerState) (bool, error) {
	searched, got := curEnv.UniFactMem.GetSpecFactNode(stmt)
	if !got {
		return false, nil
	}

	// uniConMap := map[string]parser.Fc{}
	for _, knownFact := range searched.Facts {
		// TODO： 这里要确保搜到的事实的每一位freeObj和concreteObj能对上，然后要记录一下每一位freeObj是哪个concreteObj。还要保证涉及到的Known UniFact的param都被match上了
		paramArrMap, ok, err := ver.matchStoredUniConSpecFacts(knownFact, stmt)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

		uniConMap, ok, err := ver.ValuesUnderKeyInMatchMapEqualSpec(paramArrMap, state)
		if err != nil {
			return false, err
		}
		if !ok {
			continue
		}

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

func (ver *Verifier) ValuesUnderKeyInMatchMapEqualSpec(paramArrMap map[string][]parser.Fc, state VerState) (map[string]parser.Fc, bool, error) {
	newMap := map[string]parser.Fc{}
	for key, value := range paramArrMap {
		if len(value) == 1 {
			newMap[key] = value[0]
			continue
		}

		for i := 1; i < len(value); i++ {
			ok, err := ver.fcEqualSpec(value[0], value[i], state.spec())
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
func (ver *Verifier) specFactUniWithUniConMap(knownStmt *mem.StoredUniSpecFact, uniConMap map[string]parser.Fc, state VerState) (bool, error) {
	ver.newEnv(uniConMap)
	defer ver.deleteEnvAndRetainMsg() // 万一condFact也有uniFact的检查,那就会改变env。我需要在此时能返回到原来的env

	// 传入的map必须能和所有的uniFact的param一一对应
	// e.g. 不等号传递性因此不能直接被使用，只能给传递性这个事实取个名字
	twoSlicesEqual := glob.SlicesEqualUnordered(glob.MapKeys(uniConMap), knownStmt.Fact.Params)
	if !twoSlicesEqual {
		return false, nil
	}

	for _, condFact := range knownStmt.Fact.DomFacts {
		ok, err := ver.FactStmt(condFact, state.spec().noMsg()) // TODO: 这里最好要标注一下是specFact
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
