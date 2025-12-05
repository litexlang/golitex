// Copyright 2024 Jiachen Shen.
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
func (ver *Verifier) cmpFc_Builtin_Then_Decompose_Spec(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		// return ver.equalTrueAddSuccessMsg(left, right, state, msg)
		return NewExecTrue(msg)
	}

	// if ok {
	// 	return true, nil
	// }

	// if ok, err := ver.decomposeFcFnsAndCheckEquality_WithoutState(left, right, cmp.Cmp_ByBIR); err != nil {
	// if ok, msg, err := ver.decomposeFcFnsAndCheckEquality(left, right, state, ver.FcsEqualBy_Eval_ShareKnownEqualMem); err != nil {
	return ver.decomposeFcFnsAndCheckEquality(left, right, state, ver.fcEqualSpec)

}

// Iterate over all equal facts. On each equal fact, use commutative, associative, cmp rule to compare.
func (ver *Verifier) fcEqualSpec(left ast.Obj, right ast.Obj, state *VerState) ExecRet {
	if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for curEnv := ver.Env; curEnv != nil; curEnv = curEnv.Parent {
		var equalToLeftFcs, equalToRightFcs *[]ast.Obj
		var gotLeftEqualFcs, gotRightEqualFcs bool

		equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
		equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalToRightFcs {
				return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known %s = %s", left, right), "", NewExecTrue(""))
			}
		}

		if gotLeftEqualFcs {
			rightAsStr := right.String()
			for _, equalToLeftFc := range *equalToLeftFcs {
				if equalToLeftFc.String() == rightAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToLeftFc, right, state); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftFc, right, equalToLeftFc, left), "", verRet)
				}
			}
		}

		if gotRightEqualFcs {
			leftAsStr := left.String()
			for _, equalToRightFc := range *equalToRightFcs {
				if equalToRightFc.String() == leftAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToRightFc, left, state); verRet.IsErr() {
					return verRet
				} else if verRet.IsTrue() {
					return ver.maybeAddSuccessMsgString(state, fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightFc, left, equalToRightFc, right), "", verRet)
				}
			}
		}
	}

	return NewExecUnknown("")
}

func (ver *Verifier) verTrueEqualFact_FcFnEqual_NoCheckRequirements(left, right *ast.FnObj, state *VerState) ExecRet {
	if len(left.Params) != len(right.Params) {
		return NewExecUnknown("")
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	verRet := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.FnHead, right.FnHead}, glob.BuiltinLine), state, false)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return NewExecUnknown("")
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)

		verRet := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.Params[i], right.Params[i]}, glob.BuiltinLine), state, false)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	// return newTrueVerRet("")
	return NewExecTrue("")
}

func (ver *Verifier) FcsEqualBy_Eval_ShareKnownEqualMem(left, right ast.Obj, state *VerState) ExecRet {
	for curEnv := ver.Env; curEnv != nil; curEnv = curEnv.Parent {
		leftEqualFcs, ok := curEnv.EqualMem[left.String()]
		if ok {
			rightEqualFcs, ok := curEnv.EqualMem[right.String()]
			if ok {
				if leftEqualFcs == rightEqualFcs {
					return NewExecTrue("")
				}
			}
		}
	}

	leftEqualFcs, ok := ver.Env.GetEqualFcs(left)
	if !ok {
		return NewExecUnknown("")
	}

	rightEqualFcs, ok := ver.Env.GetEqualFcs(right)
	if !ok {
		return NewExecUnknown("")
	}

	for _, leftEqualFc := range *leftEqualFcs {
		for _, rightEqualFc := range *rightEqualFcs {
			if leftEqualFc.String() == rightEqualFc.String() {
				return NewExecTrue("")
			} else {
				_, newLeft := ver.Env.ReplaceSymbolWithValue(leftEqualFc)
				if cmp.IsNumExprLitObj(newLeft) {
					_, newRight := ver.Env.ReplaceSymbolWithValue(rightEqualFc)
					if ok, _, _ := cmp.CmpBy_Literally_NumLit_PolynomialArith(newLeft, newRight); ok {
						return NewExecTrue("")
					}
				}
			}
		}
	}

	return NewExecUnknown("")
}
