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
func (ver *Verifier) cmpFc_Builtin_Then_Decompose_Spec(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return NewVerErr(err.Error())
	}
	if ok {
		// return ver.equalTrueAddSuccessMsg(left, right, state, msg)
		return NewVerTrue(msg)
	}

	// if ok {
	// 	return true, nil
	// }

	// if ok, err := ver.decomposeFcFnsAndCheckEquality_WithoutState(left, right, cmp.Cmp_ByBIR); err != nil {

	if verRet := ver.decomposeFcFnsAndCheckEquality(left, right, state, ver.fcEqualSpec); verRet.IsErr() || verRet.IsTrue() {
		// if ok, msg, err := ver.decomposeFcFnsAndCheckEquality(left, right, state, ver.FcsEqualBy_Eval_ShareKnownEqualMem); err != nil {
		return verRet
	}

	return NewVerUnknown("")
}

// Iterate over all equal facts. On each equal fact, use commutative, associative, cmp rule to compare.
func (ver *Verifier) fcEqualSpec(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		var equalToLeftFcs, equalToRightFcs *[]ast.Fc
		var gotLeftEqualFcs, gotRightEqualFcs bool

		equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
		equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalToRightFcs {
				if state.WithMsg {
					ver.successWithMsg(fmt.Sprintf("known %s = %s", left, right), "")
				}
				return NewVerTrue("")
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
					if state.WithMsg {
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftFc, right, equalToLeftFc, left), "")
					}
					return verRet
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
					if state.WithMsg {
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightFc, left, equalToRightFc, right), "")
					}
					return verRet
				}
			}
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verTrueEqualFact_FcFnEqual_NoCheckRequirements(left, right *ast.FcFn, state *VerState) VerRet {
	if len(left.Params) != len(right.Params) {
		return NewVerUnknown("")
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	verRet := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.FnHead, right.FnHead}, glob.InnerGenLine), state, false)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return NewVerUnknown("")
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)

		verRet := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.Params[i], right.Params[i]}, glob.InnerGenLine), state, false)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	// return newTrueVerRet("")
	return NewVerTrue("")
}

func (ver *Verifier) FcsEqualBy_Eval_ShareKnownEqualMem(left, right ast.Fc, state *VerState) VerRet {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		leftEqualFcs, ok := curEnv.EqualMem[left.String()]
		if ok {
			rightEqualFcs, ok := curEnv.EqualMem[right.String()]
			if ok {
				if leftEqualFcs == rightEqualFcs {
					return NewVerTrue("")
				}
			}
		}
	}

	leftEqualFcs, ok := ver.env.GetEqualFcs(left)
	if !ok {
		return NewVerUnknown("")
	}

	rightEqualFcs, ok := ver.env.GetEqualFcs(right)
	if !ok {
		return NewVerUnknown("")
	}

	for _, leftEqualFc := range *leftEqualFcs {
		for _, rightEqualFc := range *rightEqualFcs {
			if leftEqualFc.String() == rightEqualFc.String() {
				return NewVerTrue("")
			} else {
				_, newLeft := ver.env.ReplaceSymbolWithValue(leftEqualFc)
				if cmp.IsNumLitFc(newLeft) {
					_, newRight := ver.env.ReplaceSymbolWithValue(rightEqualFc)
					if ok, _, _ := cmp.CmpBy_Literally_NumLit_PolynomialArith(newLeft, newRight); ok {
						return NewVerTrue("")
					}
				}
			}
		}
	}

	return NewVerUnknown("")
}
