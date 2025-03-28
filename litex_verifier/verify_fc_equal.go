package litexverifier

import (
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) fcEqual(left, right parser.Fc, addRound bool) error {
	if addRound {
		verifier.roundAddOne()
		defer verifier.roundMinusOne()
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
		verifier.unknown("")
	}

	if fcEnum == cmp.FcAtomEnum {
		return verifier.fcAtomEqualSpec(left.(*parser.FcAtom), right.(*parser.FcAtom))
	} else if fcEnum == cmp.FcFnCallPipeEnum {
		return verifier.fcFnCallPipeEqualSpec(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe))
	}

	return nil
	// ret, err := cmp.CmpFc(left, right)
	// if err != nil {
	// 	return err
	// }
	// if ret == 0 {
	// 	if verifier.round1() {
	// 		verifier.success(fmt.Sprintf("%s = %s", left.String(), right.String()), "")
	// 	}
	// }

	// return nil
}

func (verifier *Verifier) fcAtomEqualSpec(left, right *parser.FcAtom) error {
	return nil
}

func (verifier *Verifier) fcFnCallPipeEqualSpec(left, right *parser.FcFnCallPipe) error {
	return nil
}
