package litex_verifier

import (
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
)

func (ver *Verifier) FcEqual(left, right ast.Fc, state VerState) (bool, error) {
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

func (ver *Verifier) FcEqualSpecInSpecMemLitAtEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	// ok, err := ver.FcEqualSpecInSpecMemLiterallyAtEnvWithKey(curEnv, left, right, state)
	ok, err := ver.FcEqualSpecUseEnvSpecMemRule(curEnv, left, right, state)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}
	// ok, err = ver.FcEqualSpecInSpecMemLiterallyAtEnvWithKey(curEnv, right, left, state)
	ok, err = ver.FcEqualSpecUseEnvSpecMemRule(curEnv, right, left, state)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}
	return false, nil
}

// func (ver *Verifier) FcEqualSpecInSpecMemLiterallyAtEnvWithKey(curEnv *env.Env, keyFc ast.Fc, fcToComp ast.Fc, state VerState) (bool, error) {
// 	key := memory.EqualFactMemoryTreeNode{FcAsKey: keyFc, Values: &[]ast.Fc{}}

// 	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

// 	if err != nil {
// 		return false, err
// 	}

// 	if searchedNode == nil {
// 		return false, nil
// 	}

// 	ok, err := cmpSearchNodeKeyValuesRule(searchedNode.Key.Values, fcToComp)
// 	if err != nil {
// 		return false, nil
// 	}
// 	return ok, nil
// }

func cmpSearchNodeKeyValuesRule(valuesToBeComped *[]ast.Fc, fcToComp ast.Fc) (bool, error) {
	for _, equalFc := range *valuesToBeComped {
		ok, err := cmp.CmpFcRule(equalFc, fcToComp)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) FcEqualSpecUseEnvSpecMemRule(curEnv *env.Env, keyFc ast.Fc, fcToComp ast.Fc, state VerState) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: keyFc, Values: &[]ast.Fc{}}

	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	if searchedNode == nil {
		return false, nil
	}

	key2 := memory.EqualFactMemoryTreeNode{FcAsKey: fcToComp, Values: &[]ast.Fc{}}
	searchedNode2, err := curEnv.EqualFactMem.Mem.TreeSearch(&key2)

	if err != nil {
		return false, err
	}

	if searchedNode2 != nil && searchedNode.Key != nil && searchedNode2.Key != nil {
		if searchedNode.Key.Values != nil && searchedNode.Key.Values == searchedNode2.Key.Values {
			return true, nil
		}
	}

	ok, err := cmpSearchNodeKeyValuesRule(searchedNode.Key.Values, fcToComp)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return ok, nil
}
