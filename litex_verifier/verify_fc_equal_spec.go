package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
)

func (ver *Verifier) fcEqualSpec(left, right ast.Fc, state VerState) (bool, error) {
	ok, err := cmp.CmpFcRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// Case: 用已知事实
	nextState := state.addRound()
	ok, err = ver.fcEqualSpecInSpecMem(left, right, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// Case: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		// ver.unknownNoMsg()
		return false, nil
	}

	if fcEnum == cmp.FcFnEnum {
		return ver.fcFnPipeEqual(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(left, right ast.Fc, state VerState) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := ver.FcEqualSpecInSpecMemLitAtEnv(curEnv, left, right, state)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
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
		verified, err := ver.FcEqual(knownParam, right[i], specMode)
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
