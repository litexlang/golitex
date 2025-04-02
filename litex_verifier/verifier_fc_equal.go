package litexverifier

import (
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FcEqual(left, right parser.Fc, state verState) (bool, error) {
	ver.addRound()
	defer ver.minusRound()

	// check whether given left or right is uniParam
	concreteLeft := ver.asConFc(left)
	if concreteLeft != nil {
		left = concreteLeft
	}
	concreteRight := ver.asConFc(right)
	if concreteRight != nil {
		right = concreteRight
	}

	ok, err := ver.fcEqualSpec(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	if !ver.round1() {
		return false, nil
	}

	return false, nil
}

func (ver *Verifier) FcEqualSpecInSpecMemAtEnv(curEnv *env.Env, left parser.Fc, right parser.Fc) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: left, Values: []*parser.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		cmpRet, err := cmp.CmpFcLiterally(*equalFc, right) // 只能用直接比较法
		// ok, err := ver.fcEqualSpec(*equalFc, right) // 这会导致无限循环
		if err != nil {
			return false, err
		}
		if cmpRet == 0 {
			return true, nil
		}
	}

	return false, nil
}
