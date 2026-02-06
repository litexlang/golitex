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
// func (ver *Verifier) cmpObj_Builtin_Then_Decompose_Spec(left ast.Obj, right ast.Obj, state *VerState) ast.VerRet {
// 	ret := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(left, right) // 完全一样
// 	if ret.IsErr() {
// 		return ret
// 	}
// 	if ret.IsTrue() {
// 		if state.WithMsg {
// 			return ret
// 		}
// 		return glob.NewEmptyVerRetTrue()
// 	}

// 	// return ver.decomposeObjFnsAndCheckEquality(left, right, state, ver.objEqualSpec)
// 	return ast.NewEmptyUnknownVerRet()
// }

func (ver *Verifier) decomposeObjFnsAndCheckEquality(left ast.Obj, right ast.Obj, state *VerState, areEqualObjs func(left ast.Obj, right ast.Obj, state *VerState) ast.VerRet) ast.VerRet {
	if leftAsFn, ok := left.(*ast.FnObj); ok {
		if rightAsFn, ok := right.(*ast.FnObj); ok {
			if len(leftAsFn.Params) != len(rightAsFn.Params) {
				return ast.NewEmptyUnknownVerRet()
			}

			// compare head
			verRet := areEqualObjs(leftAsFn.FnHead, rightAsFn.FnHead, state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
			// compare params
			for i := range leftAsFn.Params {
				verRet := areEqualObjs(leftAsFn.Params[i], rightAsFn.Params[i], state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet
				}
			}

			equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, glob.BuiltinLine0)
			return ast.NewTrueVerRet(equalFact, nil, fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right))
		}
	}
	return ast.NewEmptyUnknownVerRet()
}

// Iterate over all equal facts. On each equal fact, use commutative, associative, cmp rule to compare.
func (ver *Verifier) objEqualSpec(left ast.Obj, right ast.Obj, state *VerState) ast.VerRet {
	if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(left, right); verRet.IsErr() || verRet.IsTrue() {
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
				equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, glob.BuiltinLine0)
				if state.WithMsg {
					return ast.NewTrueVerRet(equalFact, nil, fmt.Sprintf("known %s = %s", left, right))
				}
				return ast.NewTrueVerRet(equalFact, nil, "")
			}
		}

		if gotLeftEqualObjs {
			rightAsStr := right.String()
			for _, equalToLeftObj := range *equalToLeftObjs {
				if equalToLeftObj.String() == rightAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(equalToLeftObj, right); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, glob.BuiltinLine0)
					if state.WithMsg {
						msg := fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftObj, right, equalToLeftObj, left)
						if len(verRet.GetExtraInfos()) > 0 {
							msg += "\n" + fmt.Sprintf("%v", verRet.GetExtraInfos())
						}
						return ast.NewTrueVerRet(equalFact, nil, msg)
					}
					return verRet
				}
			}
		}

		if gotRightEqualObjs {
			leftAsStr := left.String()
			for _, equalToRightObj := range *equalToRightObjs {
				if equalToRightObj.String() == leftAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(equalToRightObj, left); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, glob.BuiltinLine0)
					if state.WithMsg {
						msg := fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightObj, left, equalToRightObj, right)
						if len(verRet.GetExtraInfos()) > 0 {
							msg += "\n" + fmt.Sprintf("%v", verRet.GetExtraInfos())
						}
						return ast.NewTrueVerRet(equalFact, nil, msg)
					}
					return verRet
				}
			}
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) FcsEqualBy_Eval_ShareKnownEqualMem(left, right ast.Obj, state *VerState) ast.StmtRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		leftEqualObjs, ok := curEnv.EqualMem[left.String()]
		if ok {
			rightEqualObjs, ok := curEnv.EqualMem[right.String()]
			if ok {
				if leftEqualObjs == rightEqualObjs {
					return newTrueStmtRetWithCaller()
				}
			}
		}
	}

	leftEqualObjs, ok := ver.Env.GetEqualObjs(left)
	if !ok {
		return newUnknownStmtRetWithCaller("")
	}

	rightEqualObjs, ok := ver.Env.GetEqualObjs(right)
	if !ok {
		return newUnknownStmtRetWithCaller("")
	}

	for _, leftEqualObj := range *leftEqualObjs {
		for _, rightEqualObj := range *rightEqualObjs {
			if leftEqualObj.String() == rightEqualObj.String() {
				return newTrueStmtRetWithCaller()
			} else {
				_, newLeft := ver.Env.GetStoredSymbolValue(leftEqualObj)
				if cmp.IsNumExprLitObj(newLeft) {
					_, newRight := ver.Env.GetStoredSymbolValue(rightEqualObj)
					if ret := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(newLeft, newRight); ret.IsTrue() {
						return newTrueStmtRetWithCaller()
					}
				}
			}
		}
	}

	return newUnknownStmtRetWithCaller("")
}
