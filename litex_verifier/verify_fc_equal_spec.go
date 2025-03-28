package litexverifier

import (
	"fmt"
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) fcEqual(left, right parser.Fc, addRound bool) error {
	if addRound {
		verifier.addRound()
		defer verifier.minusRound()
	}

	err := verifier.fcEqualSpec(left, right)
	if err != nil {
		return nil
	}

	return nil
}

func (ver *Verifier) fcEqualSpec(left, right parser.Fc) error {
	err := ver.fcEqualSpecDirectly(left, right)
	if err != nil {
		return err
	}

	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return nil
	}

	if cmpRet != 0 {
		ver.unknownNoMsg()
	}

	if fcEnum == cmp.FcAtomEnum {
		return ver.fcAtomEqualSpec(left.(*parser.FcAtom), right.(*parser.FcAtom))
	} else if fcEnum == cmp.FcFnCallPipeEnum {
		return ver.fcFnCallPipeEqualSpec(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe))
	}

	return nil
}

func (ver *Verifier) fcEqualSpecDirectly(left, right parser.Fc) error {
	// 完全一样
	cmpRet, err := cmp.CmpFc(left, right)
	if err != nil {
		return err
	}
	if cmpRet == 0 {
		return nil
	}

	// 如果之前显式地说过 left = right，那就直接成立
	return nil
}

func (verifier *Verifier) fcAtomEqualSpec(left, right *parser.FcAtom) error {
	return nil
}

func (verifier *Verifier) fcFnCallPipeEqualSpec(left, right *parser.FcFnCallPipe) error {
	// 如果两个函数的名字一样，每个参数都一样，那也行
	ret, err := cmp.CmpFc(&left.FnHead, &right.FnHead)
	if err != nil {
		return err
	}

	if ret != 0 {
		return nil
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		if len(left.CallPipe[i].Params) != len(right.CallPipe[i].Params) {
			return nil
		}

		for j := 0; j < len(left.CallPipe[i].Params); j++ {
			err := verifier.fcEqualSpec(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j])
			if err != nil {
				return err
			}
			if !verifier.true() {
				return nil
			}
		}
	}

	if verifier.round1() {
		verifier.successMsg(fmt.Sprintf("%v = %v", left.String(), right.String()), "use known facts")
	} else {
		verifier.successNoMsg()
	}

	return nil
}
