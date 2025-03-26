package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (exec *Verifier) verifyFcEqual(left, right parser.Fc) error {
	panic("")
}

func (exec *Verifier) verifyTwoFcEqual(curEnv *env.Env, left parser.Fc, right parser.Fc) error {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: left, Values: []*parser.Fc{}}

	// searchedNode, err := SearchInEnv(curEnv, &curEnv.ConcreteEqualMemory.Mem, &key)
	searchedNode, err := curEnv.ConcreteEqualMemory.Mem.TreeSearch(&key)

	if err != nil {
		return err
	}

	comp, err := cmp.CmpFc(left, right)

	if err != nil {
		return err
	}
	if comp == 0 {
		exec.success("%s = %s, verified by %v", left, right, searchedNode.Key)
		return nil
	}

	if searchedNode == nil {
		return nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		comp, err := cmp.CmpFc(right, *equalFc)
		if err != nil {
			return err
		}
		if comp == 0 {
			exec.success("%s = %s, verified by %v", left, right, equalFc)
			return nil
		}
	}

	return nil
}

func (exec *Verifier) verifyEqualFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	return exec.verifyTwoFcEqual(curEnv, stmt.Params[0], stmt.Params[1])
}

func (verifier *Verifier) twoParamSliceHaveEqualParams(left *[]parser.Fc, right *[]parser.Fc) (bool, error) {

	// TODO: 25-3-26: 这里检查长度，未来确定不能让不同长度的f出现时，我去掉这一条
	if len(*left) != len(*right) {
		return false, fmt.Errorf("%v and %v have different length", *left, *right)
	}

	twoFuncFactHaveEqualParams := true
	for i, knownParam := range *left {
		err := verifier.verifyFcEqual(knownParam, (*left)[i])
		if err != nil {
			return false, err
		}
		if !verifier.true() {
			twoFuncFactHaveEqualParams = false
			break
		}
	}

	if twoFuncFactHaveEqualParams {
		return true, nil
	}

	return false, nil
}
