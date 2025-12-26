// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

// SERIOUS BUG
// WARNING
// REMARK
// TODO: cmpFc_Builtin_Then_Decompose_Spec, fcEqualSpec 大循环本质上是有问题的，会有循环论证的风险：know p(p(1,2), 0) = 1, 则现在问 p(1,2) =1 吗？我会比较 p(1,2) = p(p(1,2), 0)，那这时候就出问题了：我因为一位位地比，所以又回到了比较 1 = p(1,2)
func (ver *Verifier) cmpObj_Builtin_Then_Decompose_Spec(left ast.Obj, right ast.Obj, state *VerState) *glob.GlobRet {
	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if ok {
		// return ver.equalTrueAddSuccessMsg(left, right, state, msg)
		return glob.NewGlobTrueWithStmt(msg)
	}

	// if ok {
	// 	return true, nil
	// }

	// if ok, err := ver.decomposeFcFnsAndCheckEquality_WithoutState(left, right, cmp.Cmp_ByBIR); err != nil {
	// if ok, msg, err := ver.decomposeFcFnsAndCheckEquality(left, right, state, ver.FcsEqualBy_Eval_ShareKnownEqualMem); err != nil {
	return ver.decomposeObjFnsAndCheckEquality(left, right, state, ver.objEqualSpec)

}

// Iterate over all equal facts. On each equal fact, use commutative, associative, cmp rule to compare.
func (ver *Verifier) objEqualSpec(left ast.Obj, right ast.Obj, state *VerState) *glob.GlobRet {
	if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		var equalToLeftObjs, equalToRightObjs *[]ast.Obj
		var gotLeftEqualObjs, gotRightEqualObjs bool

		equalToLeftObjs, gotLeftEqualObjs = curEnv.GetEqualObjs(left)
		equalToRightObjs, gotRightEqualObjs = curEnv.GetEqualObjs(right)

		if gotLeftEqualObjs && gotRightEqualObjs {
			if equalToLeftObjs == equalToRightObjs {
				return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known %s = %s", left, right), "", glob.NewEmptyGlobTrue())
			}
		}

		if gotLeftEqualObjs {
			rightAsStr := right.String()
			for _, equalToLeftObj := range *equalToLeftObjs {
				if equalToLeftObj.String() == rightAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(equalToLeftObj, right, state); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftObj, right, equalToLeftObj, left), "", verRet)
				}
			}
		}

		if gotRightEqualObjs {
			leftAsStr := left.String()
			for _, equalToRightObj := range *equalToRightObjs {
				if equalToRightObj.String() == leftAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := ver.cmpObj_Builtin_Then_Decompose_Spec(equalToRightObj, left, state); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightObj, left, equalToRightObj, right), "", verRet)
				}
			}
		}
	}

	return glob.NewEmptyGlobUnknown()
}

func (ver *Verifier) verTrueEqualFact_ObjFnEqual_NoCheckRequirements(left, right *ast.FnObj, state *VerState) *glob.GlobRet {
	if len(left.Params) != len(right.Params) {
		return glob.NewEmptyGlobUnknown()
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.FnHead, right.FnHead}, glob.BuiltinLine), state.CopyAndReqOkToTrue())
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyGlobUnknown()
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)

		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.Params[i], right.Params[i]}, glob.BuiltinLine), state.CopyAndReqOkToTrue())
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	// return newTrueVerRet("")
	return glob.NewEmptyGlobTrue()
}

func (ver *Verifier) FcsEqualBy_Eval_ShareKnownEqualMem(left, right ast.Obj, state *VerState) *glob.GlobRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		leftEqualObjs, ok := curEnv.EqualMem[left.String()]
		if ok {
			rightEqualObjs, ok := curEnv.EqualMem[right.String()]
			if ok {
				if leftEqualObjs == rightEqualObjs {
					return glob.NewEmptyGlobTrue()
				}
			}
		}
	}

	leftEqualObjs, ok := ver.Env.GetEqualObjs(left)
	if !ok {
		return glob.NewEmptyGlobUnknown()
	}

	rightEqualObjs, ok := ver.Env.GetEqualObjs(right)
	if !ok {
		return glob.NewEmptyGlobUnknown()
	}

	for _, leftEqualObj := range *leftEqualObjs {
		for _, rightEqualObj := range *rightEqualObjs {
			if leftEqualObj.String() == rightEqualObj.String() {
				return glob.NewEmptyGlobTrue()
			} else {
				_, newLeft := ver.Env.ReplaceSymbolWithValue(leftEqualObj)
				if cmp.IsNumExprLitObj(newLeft) {
					_, newRight := ver.Env.ReplaceSymbolWithValue(rightEqualObj)
					if ok, _, _ := cmp.CmpBy_Literally_NumLit_PolynomialArith(newLeft, newRight); ok {
						return glob.NewEmptyGlobTrue()
					}
				}
			}
		}
	}

	return glob.NewEmptyGlobUnknown()
}
