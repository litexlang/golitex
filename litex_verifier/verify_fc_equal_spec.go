package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FcEqual(left, right parser.Fc, addRound bool) (bool, error) {
	if addRound {
		ver.addRound()
		defer ver.minusRound()
	}

	ok, err := ver.fcEqualSpec(left, right)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}

	if !ver.round1() {
		return false, nil
	}

	return false, nil
}

func (ver *Verifier) fcEqualSpec(left, right parser.Fc) (bool, error) {
	// Case: 完全一样
	cmpRet, err := cmp.CmpFc(left, right)
	if err != nil {
		return false, err
	}
	if cmpRet == 0 {
		return true, nil
	}

	ok, err := ver.fcEqualSpecInSpecMem(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, nil
	}

	if cmpRet != 0 {
		ver.unknownNoMsg()
	}

	if fcEnum == cmp.FcAtomEnum {
		return ver.fcAtomEqualSpec(left.(*parser.FcAtom), right.(*parser.FcAtom))
	} else if fcEnum == cmp.FcFnCallPipeEnum {
		return ver.fcFnCallPipeEqualSpec(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe))
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(left, right parser.Fc) (bool, error) {
	// 如果之前显式地说过 left = right，那就直接成立
	return false, nil
}

func (ver *Verifier) fcAtomEqualSpec(left, right *parser.FcAtom) (bool, error) {
	return false, nil
}

func (ver *Verifier) fcFnCallPipeEqualSpec(left, right *parser.FcFnCallPipe) (bool, error) {
	// 如果两个函数的名字一样，每个参数都一样，那也行
	ret, err := cmp.CmpFc(&left.FnHead, &right.FnHead)
	if err != nil {
		return false, err
	}

	if ret != 0 {
		return false, nil
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return false, nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		if len(left.CallPipe[i].Params) != len(right.CallPipe[i].Params) {
			return false, nil
		}

		for j := 0; j < len(left.CallPipe[i].Params); j++ {
			ver.unknownNoMsg() // clear verifier
			ok, err := ver.fcEqualSpec(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j])
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
	}

	if ver.round1() {
		ver.successMsg(fmt.Sprintf("%v = %v", left.String(), right.String()), "use known facts")
	} else {
		ver.successNoMsg()
	}

	return true, nil
}
