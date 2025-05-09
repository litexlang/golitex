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
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (ver *Verifier) equalFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.IsValidEqualFact() {
		return false, nil
	}

	isSuccess := false
	defer func() {
		if state.requireMsg() && isSuccess {
			ver.successMsgEnd(stmt.String(), "")
		}
	}()

	left := stmt.Params[0]
	right := stmt.Params[1]

	// Case: 用内置方法直接比较，比如计算字面量都是整数，那可以通过运算来比较
	ok, err := cmp.CmpFcRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		isSuccess = true
		return true, nil
	}

	// Case: 用Meme里找
	if ok, err := ver.equalByEqualMem(left, right); err != nil {
		return false, err
	} else if ok {
		isSuccess = true
		return true, nil
	}

	// Case: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		return false, nil
	}

	if fcEnum == cmp.FcFnEnum {
		// WARNING:  这里根本不是SpecMsg，而是RoundMsg，所以fcEqualSpec里不能是可能用到非SpecFact的
		// state = state.addRound()
		return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), state.toSpec())
		// return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return isSuccess, nil
}

func (ver *Verifier) equalByEqualMem(left ast.Fc, right ast.Fc) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		equalToLeftFcs, gotLeftEqualFcs := curEnv.GetEqualFcs(left)
		equalTorightFcs, gotRightEqualFcs := curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalTorightFcs {
				return true, nil
			}
		}

		if gotLeftEqualFcs {
			for _, equalToLeftFc := range *equalToLeftFcs {
				ok, err := cmp.CmpFcRule(equalToLeftFc, right)
				if err != nil {
					return false, err
				}
				if ok {
					return true, nil
				}
			}
		}

		if gotRightEqualFcs {
			for _, equalToRightFc := range *equalTorightFcs {
				ok, err := cmp.CmpFcRule(equalToRightFc, left)
				if err != nil {
					return false, err
				}
				if ok {
					return true, nil
				}
			}
		}
	}

	return false, nil
}
