package litex_verifier

import ast "golitex/litex_ast"

func (ver *Verifier) fcFnPipeEqual(left, right *ast.FcFnPipe, state VerState) (bool, error) {
	for leftTailLen := 0; leftTailLen <= len(left.CallPipe); leftTailLen++ {
		ok, err := ver.fcFnPipeHeadTailEqual(left, right, state, leftTailLen)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) fcFnPipeHeadTailEqual(left, right *ast.FcFnPipe, state VerState, leftTailLen int) (bool, error) {
	if leftTailLen == 0 { // 必须存在，否则死循环
		if len(left.CallPipe) != len(right.CallPipe) {
			return false, nil
		}

		for i := 0; i < len(left.CallPipe); i++ {
			// ? 这里应该是fcEqualSpec还是 fcCmpLiterally??
			ok, err := ver.fcEqualSpec(&left.FnHead, &right.FnHead, state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}

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

	var leftHead ast.Fc
	if leftHeadLen == 0 {
		leftHead = &left.FnHead
	} else {
		leftHead = &ast.FcFnPipe{FnHead: left.FnHead, CallPipe: left.CallPipe[:leftHeadLen]}
	}

	var rightHead ast.Fc
	if rightHeadLen == 0 {
		rightHead = &right.FnHead
	} else {
		rightHead = &ast.FcFnPipe{FnHead: right.FnHead, CallPipe: right.CallPipe[:rightHeadLen]}
	}

	ok, err := ver.fcHeadEqual(leftHead, rightHead, leftTails[0].Params, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) fcHeadEqual(leftHead ast.Fc, rightHead ast.Fc, params []ast.Fc, state VerState) (bool, error) {
	ok, err := ver.FcEqual(leftHead, rightHead, state)
	_ = params
	return ok, err

	// TODO 以后引入新的keyword专门用来证明函数头相等，2个函数在params所在的某domain里，刚好相等? 或者我还是不引入？
}
