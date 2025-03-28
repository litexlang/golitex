package litexverifier

import (
	"fmt"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (ver *Verifier) TwoFcEqualSpec(left, right parser.Fc) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := ver.TwoFcEqualSpecAtEnv(curEnv, left, right)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) TwoFcEqualSpecAtEnv(curEnv *env.Env, left parser.Fc, right parser.Fc) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: left, Values: []*parser.Fc{}}

	// searchedNode, err := SearchInEnv(curEnv, &curEnv.ConcreteEqualMemory.Mem, &key)
	searchedNode, err := curEnv.EqualFactMem.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	ok, err := ver.FcEqual(left, right, true)

	if err != nil {
		return false, err
	}
	if ok {
		// verifier.newMessage("true:%v = %v", left.String(), right.String())
		return true, nil
	}

	if searchedNode == nil {
		return false, nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		ok, err := ver.FcEqual(*equalFc, right, true)
		if err != nil {
			return false, err
		}
		if ok {
			// verifier.newMessage("true:%v = %v", left.String(), right.String())
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) FcSliceEqualSpec(left *[]parser.Fc, right *[]parser.Fc) (bool, error) {

	// TODO: 25-3-26: 这里检查长度，未来确定不能让不同长度的f出现时，我去掉这一条
	if len(*left) != len(*right) {
		return false, fmt.Errorf("%v and %v have different length", *left, *right)
	}

	twoFuncFactHaveEqualParams := true
	for i, knownParam := range *left {
		verified, err := ver.TwoFcEqualSpec(knownParam, (*right)[i])
		if err != nil {
			return false, err
		}
		if !verified {
			twoFuncFactHaveEqualParams = false
			break
		}
	}

	if twoFuncFactHaveEqualParams {
		return true, nil
	}

	return false, nil
}
