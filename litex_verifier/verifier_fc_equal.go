package litexverifier

import (
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FcEqual(left, right parser.Fc, state VerState) (bool, error) {
	// check whether given left or right is uniParam
	concreteLeft := ver.asConFc(left)
	if concreteLeft != nil {
		left = concreteLeft
	}
	concreteRight := ver.asConFc(right)
	if concreteRight != nil {
		right = concreteRight
	}

	nextState := state.spec()
	ok, err := ver.fcEqualSpec(left, right, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	// TODO 用 UniFact ? CondFact?

	return false, nil
}

func (ver *Verifier) FcEqualSpecInSpecMemLiterallyAtEnv(curEnv *env.Env, left parser.Fc, right parser.Fc, state VerState) (bool, error) {
	ok, err := ver.FcEqualSpecInSpecMemLiterallyAtEnvWithKey(curEnv, left, right, state)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}
	ok, err = ver.FcEqualSpecInSpecMemLiterallyAtEnvWithKey2(curEnv, right, left, state)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) FcEqualSpecInSpecMemLiterallyAtEnvWithKey(curEnv *env.Env, keyFc parser.Fc, fcToComp parser.Fc, state VerState) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: keyFc, Values: &[]parser.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	ok, err := cmpSearchNodeKeyValuesLiterally(searchedNode.Key.Values, fcToComp)
	if err != nil {
		return false, nil
	}
	return ok, nil
}

func cmpSearchNodeKeyValuesLiterally(valuesToBeComped *[]parser.Fc, fcToComp parser.Fc) (bool, error) {
	for _, equalFc := range *valuesToBeComped {
		// TODO? 貌似不需要在每个key下面存一个数组；我只要让这些key下面有共同的signal，这些signal一致，就行。
		cmpRet, err := cmp.CmpFcLiterally(equalFc, fcToComp) // 只能用直接比较法
		// ok, err := ver.fcEqualSpec(*equalFc, toBeCompared) // 这会导致无限循环
		if err != nil {
			return false, err
		}
		if cmpRet == 0 {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) FcEqualSpecInSpecMemLiterallyAtEnvWithKey2(curEnv *env.Env, keyFc parser.Fc, fcToComp parser.Fc, state VerState) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: keyFc, Values: &[]parser.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	key2 := memory.EqualFactMemoryTreeNode{FcAsKey: fcToComp, Values: &[]parser.Fc{}}

	searchedNode2, err := curEnv.EqualFactMem.Mem.TreeSearch(&key2)

	if err != nil {
		return false, err
	}

	if searchedNode2 == nil {
		return false, nil
	}

	if searchedNode.Key.Values == searchedNode2.Key.Values {
		return true, nil
	} else {
		return false, nil
	}
}
