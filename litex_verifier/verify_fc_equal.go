package litexverifier

import (
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
	// 如果之前显式地说过 left = right，那就直接成立
	return nil
}

func (verifier *Verifier) fcAtomEqualSpec(left, right *parser.FcAtom) error {
	return nil
}

func (verifier *Verifier) fcFnCallPipeEqualSpec(left, right *parser.FcFnCallPipe) error {
	return nil
}
