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

func (verifier *Verifier) fcEqualSpec(left, right parser.Fc) error {
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return nil
	}

	if cmpRet != 0 {
		// 如果是 atom 和 fn 基于 spec 比，那只能是刚好一样了
		if cmpRet < 0 { // left FcAtom, right FcFn
			return verifier.fcLeftAtomRightFn(left.(*parser.FcAtom), right.(*parser.FcFnCallPipe))
		} else {
			return verifier.fcLeftAtomRightFn(right.(*parser.FcAtom), right.(*parser.FcFnCallPipe))
		}
	}

	if fcEnum == cmp.FcAtomEnum {
		return verifier.fcAtomEqualSpec(left.(*parser.FcAtom), right.(*parser.FcAtom))
	} else if fcEnum == cmp.FcFnCallPipeEnum {
		return verifier.fcFnCallPipeEqualSpec(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe))
	}

	return nil
}

func (verifier *Verifier) fcAtomEqualSpec(left, right *parser.FcAtom) error {
	return nil
}

func (verifier *Verifier) fcFnCallPipeEqualSpec(left, right *parser.FcFnCallPipe) error {
	return nil
}

func (ver *Verifier) fcLeftAtomRightFn(left *parser.FcAtom, right *parser.FcFnCallPipe) error {
	return nil
}
