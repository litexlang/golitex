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
	cmp "golitex/cmp"
)

func (ver *Verifier) equalFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := stmt.IsValidEqualFact(); err != nil {
		return false, err
	} else if !ok {
		return false, nil
	}
	return ver.fcEqual(stmt.Params[0], stmt.Params[1], state)
}

func (ver *Verifier) fcEqual(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	isSuccess := false
	defer func() {
		if state.requireMsg() && isSuccess {
			ver.successMsgEnd(fmt.Sprintf("%s = %s", left.String(), right.String()), "")
		}
	}()

	// Case1: 用内置方法直接比较，比如计算字面量都是整数，那可以通过运算来比较
	ok, err := ver.fcEqual_Commutative_Associative_CmpRule(left, right, state)
	if err != nil {
		return false, err
	}
	if ok {
		isSuccess = true
		return true, nil
	}

	// Case2: 用Mem里找
	if ok, err := ver.equalByEqualMem(left, right); err != nil {
		return false, err
	} else if ok {
		isSuccess = true
		return true, nil
	}

	// Case3: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		return false, nil
	}

	// 总之这里估计是有待提高的
	if fcEnum == cmp.FcFnEnum {
		// WARNING:  这里根本不是SpecMsg，而是RoundMsg，所以fcEqualSpec里不能是可能用到非SpecFact的
		// state = state.addRound()
		return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), state.toSpec())
		// return ver.fcFnEq(left.(*ast.FcFn), right.(*ast.FcFn), SpecMsg)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return false, nil
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
