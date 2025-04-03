package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) fcFnPipeEqual(left, right *parser.FcFnPipe, state VerState) (bool, error) {
	for leftTailLen := 0; leftTailLen <= len(left.CallPipe); leftTailLen++ {
		ok, err := ver.fcFnPipeHeadTailEqual(left, right, state, leftTailLen)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	// return true,nil
	return false, nil
}

func (ver *Verifier) fcFnPipeHeadTailEqual(left, right *parser.FcFnPipe, state VerState, leftTailLen int) (bool, error) {
	if leftTailLen == 0 { // 必须存在，否则死循环
		if len(left.CallPipe) != len(right.CallPipe) {
			return false, nil
		}

		for i := 0; i < len(left.CallPipe); i++ {
			if len(left.CallPipe[i].Params) != len(right.CallPipe[i].Params) {
				return false, nil
			}

			for j := 0; j < len(left.CallPipe[i].Params); j++ {
				ok, err := ver.FcEqual(left.CallPipe[i].Params[j], right.CallPipe[i].Params[j], state)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
				}
			}
		}

		return true, nil
	}

	leftHeadLen := len(left.CallPipe) - leftTailLen
	rightHeadLen := len(right.CallPipe) - leftTailLen
	if rightHeadLen < 0 {
		return false, nil
	}

	leftTails := left.CallPipe[leftHeadLen:]
	rightTails := right.CallPipe[rightHeadLen:]

	for i := 0; i < leftTailLen; i++ {
		curLen := len(leftTails[i].Params)
		if curLen != len(rightTails[i].Params) {
			return false, nil
		}

		for j := 0; j < curLen; j++ {
			ok, err := ver.FcEqual(leftTails[i].Params[j], rightTails[i].Params[j], state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		}
	}

	var leftHead parser.Fc
	if leftHeadLen == 0 {
		leftHead = &left.FnHead
	} else {
		leftHead = &parser.FcFnPipe{FnHead: left.FnHead, CallPipe: left.CallPipe[:leftHeadLen]}
	}

	var rightHead parser.Fc
	if rightHeadLen == 0 {
		rightHead = &right.FnHead
	} else {
		rightHead = &parser.FcFnPipe{FnHead: right.FnHead, CallPipe: right.CallPipe[:rightHeadLen]}
	}

	ok, err := ver.FcEqual(leftHead, rightHead, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}
