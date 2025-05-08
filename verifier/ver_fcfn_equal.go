// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) fcFnEq(left, right *ast.FcFn, state VerState) (bool, error) {
	state = state.addRound()

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

	_ = state.toNoMsg()
	for i := range leftTailLen {
		curLen := len(leftTails[i])
		if curLen != len(rightTails[i]) {
			return false, nil
		}

		for j := range curLen {
			ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(leftTails[i][j], rightTails[i][j])
			// ok, err := ver.makeFcEqualFactAndVerify(leftTails[i][j], rightTails[i][j], curState)
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
		leftHead = left.FnHead
	} else {
		leftHead = &ast.FcFn{FnHead: left.FnHead, ParamSegs: left.ParamSegs[:leftHeadLen]}
	}

	var rightHead ast.Fc
	if rightHeadLen == 0 {
		rightHead = right.FnHead
	} else {
		rightHead = &ast.FcFn{FnHead: right.FnHead, ParamSegs: right.ParamSegs[:rightHeadLen]}
	}

	// ok, err := ver.makeFcEqualFactAndVerify(leftHead, rightHead, curState)
	ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(leftHead, rightHead)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successMsgEnd(fmt.Sprintf("%s = %s", left.String(), right.String()), fmt.Sprintf("%s = %s\n%s = %s", leftHead.String(), rightHead.String(), left.String(), right.String()))
	}

	return true, nil
}

func (ver *Verifier) fcFnHeadEqLeftTailLenIs0(left, right *ast.FcFn, state VerState) (bool, error) {
	// ? 这里应该是fcEqualSpec还是 fcCmpLiterally??
	if len(left.ParamSegs) != len(right.ParamSegs) {
		return false, nil
	}

	_ = state.toNoMsg()

	// ok, err := ver.makeFcEqualFactAndVerify(left.FnHead, right.FnHead, state)
	ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(left.FnHead, right.FnHead)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	for i := range left.ParamSegs {
		if len(left.ParamSegs[i]) != len(right.ParamSegs[i]) {
			return false, nil
		}

		for j := range left.ParamSegs[i] {
			// ok, err := ver.makeFcEqualFactAndVerify(left.ParamSegs[i][j], right.ParamSegs[i][j], curState)
			// 这里相当于强行只能用 specFact 来证明，不能用forall来证；如果是用forall的话，就需要 makeFcEqualFactAndVerify
			ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(left.ParamSegs[i][j], right.ParamSegs[i][j])
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
