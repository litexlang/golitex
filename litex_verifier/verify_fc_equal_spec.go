package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (ver *Verifier) fcEqualSpec(left, right parser.Fc) (bool, error) {
	// Case: 全部都是builtin类型：int,float

	// Case: 完全一样
	cmpRet, err := cmp.CmpFcLiterally(left, right)
	if err != nil {
		return false, err
	}
	if cmpRet == 0 {
		return true, nil
	}

	// Case: 用已知事实
	ok, err := ver.fcEqualSpecInSpecMem(left, right)
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
		ver.unknownNoMsg()
		return false, nil
	}

	if fcEnum == cmp.FcFnCallPipeEnum {
		return ver.fcFnCallPipeEqual(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe), true)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(left, right parser.Fc) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := ver.FcEqualSpecInSpecMemAtEnv(curEnv, left, right)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) FcSliceEqual(left []parser.Fc, right []parser.Fc, specMode bool) (bool, error) {
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
