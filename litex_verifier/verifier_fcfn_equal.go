package litex_verifier

import ast "golitex/litex_ast"

func (ver *Verifier) fcFnPipeEqual(left, right *ast.FcFn, state VerState) (bool, error) {
	for leftTailLen := 0; leftTailLen <= len(left.ParamSegs); leftTailLen++ {
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

func (ver *Verifier) fcFnPipeHeadTailEqual(left, right *ast.FcFn, state VerState, leftTailLen int) (bool, error) {
	if leftTailLen == 0 { // 必须存在，否则死循环
		if len(left.ParamSegs) != len(right.ParamSegs) {
			return false, nil
		}

		for i := 0; i < len(left.ParamSegs); i++ {
			// ? 这里应该是fcEqualSpec还是 fcCmpLiterally??
			ok, err := ver.fcEqualSpec(&left.FnHead, &right.FnHead, state)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}

			if len(left.ParamSegs[i].Params) != len(right.ParamSegs[i].Params) {
				return false, nil
			}

			for j := 0; j < len(left.ParamSegs[i].Params); j++ {
				ok, err := ver.FcEqual(left.ParamSegs[i].Params[j], right.ParamSegs[i].Params[j], state)
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

	leftHeadLen := len(left.ParamSegs) - leftTailLen
	rightHeadLen := len(right.ParamSegs) - leftTailLen
	if rightHeadLen < 0 {
		return false, nil
	}

	leftTails := left.ParamSegs[leftHeadLen:]
	rightTails := right.ParamSegs[rightHeadLen:]

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
		leftHead = &ast.FcFn{FnHead: left.FnHead, ParamSegs: left.ParamSegs[:leftHeadLen]}
	}

	var rightHead ast.Fc
	if rightHeadLen == 0 {
		rightHead = &right.FnHead
	} else {
		rightHead = &ast.FcFn{FnHead: right.FnHead, ParamSegs: right.ParamSegs[:rightHeadLen]}
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
