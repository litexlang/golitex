package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	env "golitex/litex_env"
	memory "golitex/litex_memory"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyTwoFcEqual(left, right parser.Fc) (bool, error) {
	for curEnv := verifier.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := verifier.verifyTwoFcEqualAtGivenEnv(curEnv, left, right)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

func (exec *Verifier) verifyTwoFcEqualAtGivenEnv(curEnv *env.Env, left parser.Fc, right parser.Fc) (bool, error) {
	key := memory.EqualFactMemoryTreeNode{FcAsKey: left, Values: []*parser.Fc{}}

	// searchedNode, err := SearchInEnv(curEnv, &curEnv.ConcreteEqualMemory.Mem, &key)
	searchedNode, err := curEnv.ConcreteEqualMemory.Mem.TreeSearch(&key)

	if err != nil {
		return false, err
	}

	comp, err := cmp.CmpFc(left, right)

	if err != nil {
		return false, err
	}
	if comp == 0 {
		return true, nil
	}

	if searchedNode == nil {
		return false, nil
	}

	for _, equalFc := range searchedNode.Key.Values {
		comp, err := cmp.CmpFc(right, *equalFc)
		if err != nil {
			return false, err
		}
		if comp == 0 {
			return true, nil
		}
	}

	return false, nil
}

func (verifier *Verifier) verifyEqualFactSpecifically(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	verified, err := verifier.verifyTwoFcEqualAtGivenEnv(curEnv, stmt.Params[0], stmt.Params[1])
	if err != nil {
		return err
	}
	if verified {
		verifier.success("%v is true, verified by %v", stmt, stmt.Params[0])
		return nil
	}
	return nil
}

func (verifier *Verifier) twoParamSliceHaveEqualParams(left *[]parser.Fc, right *[]parser.Fc) (bool, error) {

	// TODO: 25-3-26: 这里检查长度，未来确定不能让不同长度的f出现时，我去掉这一条
	if len(*left) != len(*right) {
		return false, fmt.Errorf("%v and %v have different length", *left, *right)
	}

	twoFuncFactHaveEqualParams := true
	for i, knownParam := range *left {
		verified, err := verifier.verifyTwoFcEqual(knownParam, (*left)[i])
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
