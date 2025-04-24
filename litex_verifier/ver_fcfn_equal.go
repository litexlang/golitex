// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
)

func (ver *Verifier) fcFnEq(left, right *ast.FcFn, state VerState) (bool, error) {
	for leftTailLen := 0; leftTailLen <= len(left.ParamSegs); leftTailLen++ {
		ok, err := ver.fcFnHeadTailEq(left, right, state, leftTailLen)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) fcFnHeadTailEq(left, right *ast.FcFn, state VerState, leftTailLen int) (bool, error) {
	if left.IsEmptyFcFn() || right.IsEmptyFcFn() {
		if state.requireMsg() {
			ver.env.NewMsg(fmt.Sprintf("TODO: fcFnEq: left is empty, right is empty is not implemented. left: %s, right: %s", left.String(), right.String()))
		}
		return false, nil
	}

	if leftTailLen == 0 { // 必须存在，否则死循环
		return ver.fcFnHeadEqLeftTailLenIs0(left, right, state)
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
			ok, err := ver.fcEqual(leftTails[i].Params[j], rightTails[i].Params[j], state)
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

	ok, err := ver.fcHeadEq(leftHead, rightHead, leftTails[0].Params, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) fcHeadEq(leftHead ast.Fc, rightHead ast.Fc, params []ast.Fc, state VerState) (bool, error) {
	ok, err := ver.fcEqual(leftHead, rightHead, state)
	_ = params
	return ok, err

	// TODO 以后引入新的keyword专门用来证明函数头相等，2个函数在params所在的某domain里，刚好相等? 或者我还是不引入？
}

func (ver *Verifier) fcFnHeadEqLeftTailLenIs0(left, right *ast.FcFn, state VerState) (bool, error) {
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
			ok, err := ver.fcEqualSpec(left.ParamSegs[i].Params[j], right.ParamSegs[i].Params[j], state)
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
