package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (ver *Verifier) FcEqual(left, right parser.Fc) (bool, error) {
	ver.addRound()
	defer ver.minusRound()

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

func (ver *Verifier) fcFnCallPipeEqual(left, right *parser.FcFnCallPipe, specMode bool) (bool, error) {
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
			var ok bool
			if specMode {
				ok, err = ver.fcEqualSpec(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j])
			} else {
				ok, err = ver.FcEqual(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j])
			}
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
