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
	env "golitex/environment"
	glob "golitex/glob"
)

// how equality is verified is different from other facts because 1. it is stored differently 2. its transitive and commutative property is automatically used by the verifier
func (ver *Verifier) verTrueEqualFact(stmt *ast.SpecFactStmt, state *VerState, checkRequirements bool) VerRet {
	if verRet := ver.verByReplaceFcInSpecFactWithValue(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if verRet := ver.verTrueEqualFactMainLogic(stmt, state, checkRequirements); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if verRet := ver.verByReplaceFcInSpecFactWithValueAndCompute(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState, checkRequirements bool) VerRet {
	var verRet VerRet

	if checkRequirements && !state.ReqOk {
		// REMARK: 这里 state 更新了： ReqOk 更新到了 true
		if state, verRet = ver.checkFnsReqAndUpdateReqState(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		if !isValidEqualFact(stmt) {
			return NewVerErr(fmt.Sprintf("invalid equal fact: %s", stmt))
		}
	}

	if verRet := ver.verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(stmt.Params[0], stmt.Params[1], state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if leftAsFn, ok := stmt.Params[0].(*ast.FcFn); ok {
		if rightAsFn, ok := stmt.Params[1].(*ast.FcFn); ok {
			verRet := ver.verTrueEqualFact_FcFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	} else {
		return NewVerUnknown("")
	}

	return NewVerUnknown("")
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && string(stmt.PropName) == glob.KeySymbolEqual
}

func (ver *Verifier) verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	if verRet := ver.verEqualBuiltin(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualSpecMem(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verLogicMem_leftToRight_RightToLeft(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}

		if verRet := ver.verEqualUniMem(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verEqualBuiltin(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return NewVerErr(err.Error())
	}
	if ok {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), msg)
		}
		return NewVerTrue("")
	}

	// 如果是 fn 那就层层盘剥
	nextState := state.GetNoMsg()
	if verRet := ver.decomposeFcFnsAndCheckEquality(left, right, nextState, ver.verEqualBuiltin); verRet.IsErr() {
		return verRet
	} else if verRet.IsTrue() {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), "each item of %s and %s are equal correspondingly")
		}
		return verRet
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verEqualSpecMem(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verRet := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return NewVerTrue("")
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state *VerState) VerRet {
	nextState := state.GetNoMsg()

	verRet := ver.getEqualFcsAndCmpOneByOne(curEnv, left, right, nextState)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), verRet.String())
		}
		return verRet
	}

	return NewVerUnknown("")
}

func (ver *Verifier) verLogicMem_leftToRight_RightToLeft(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_ByLogicMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return NewVerErr(err.Error())
	}
	verRet = ver.verSpecFact_ByLogicMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return NewVerUnknown("")
}

func (ver *Verifier) verEqualUniMem(left ast.Fc, right ast.Fc, state *VerState) VerRet {
	equalFact := ast.NewEqualFact(left, right)
	verRet := ver.verSpecFact_UniMem(equalFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return NewVerErr(err.Error())
	}
	verRet = ver.verSpecFact_UniMem(equalFactParamReversed, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}
	return NewVerUnknown("")
}

func (ver *Verifier) getEqualFcsAndCmpOneByOne(curEnv *env.Env, left ast.Fc, right ast.Fc, state *VerState) VerRet {
	var equalToLeftFcs, equalToRightFcs *[]ast.Fc
	var gotLeftEqualFcs, gotRightEqualFcs bool

	equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
	equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

	if gotLeftEqualFcs && gotRightEqualFcs {
		if equalToLeftFcs == equalToRightFcs {
			return NewVerTrue(fmt.Sprintf("%s = %s, by either their equality is known, or it is ensured by transitivity of equality.", left, right))
		}
	}

	if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if gotLeftEqualFcs {
		for _, equalToLeftFc := range *equalToLeftFcs {
			if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToLeftFc, right, state); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return NewVerTrue(fmt.Sprintf("It is true that:\n%s = %s and %s = %s", equalToLeftFc, right, equalToLeftFc, left))
			}
		}
	}

	if gotRightEqualFcs {
		for _, equalToRightFc := range *equalToRightFcs {
			if verRet := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToRightFc, left, state); verRet.IsErr() {
				return verRet
			} else if verRet.IsTrue() {
				return NewVerTrue(fmt.Sprintf("It is true that\n%s = %s and %s = %s", left, equalToRightFc, equalToRightFc, right))
			}
		}
	}

	return NewVerUnknown("")
}

func (ver *Verifier) decomposeFcFnsAndCheckEquality(left ast.Fc, right ast.Fc, state *VerState, areEqualFcs func(left ast.Fc, right ast.Fc, state *VerState) VerRet) VerRet {
	if leftAsFn, ok := left.(*ast.FcFn); ok {
		if rightAsFn, ok := right.(*ast.FcFn); ok {
			if len(leftAsFn.Params) != len(rightAsFn.Params) {
				return NewVerUnknown("")
			}

			// compare head
			verRet := areEqualFcs(leftAsFn.FnHead, rightAsFn.FnHead, state)
			if verRet.IsErr() || verRet.IsUnknown() {
				return verRet
			}
			// compare params
			for i := range leftAsFn.Params {
				verRet := areEqualFcs(leftAsFn.Params[i], rightAsFn.Params[i], state)
				if verRet.IsErr() || verRet.IsUnknown() {
					return verRet
				}
			}

			return NewVerTrue(fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right))
		}
	}
	return NewVerUnknown("")
}
