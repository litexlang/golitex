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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	env "golitex/environment"
	glob "golitex/glob"
)

// how equality is verified is different from other facts because 1. it is stored differently 2. its transitive and commutative property is automatically used by the verifier
func (ver *Verifier) verTrueEqualFact(stmt *ast.SpecFactStmt, state *VerState, checkRequirements bool) (bool, error) {
	if ok, err := (ver.verByReplaceFcInSpecFactWithValue(stmt, state)); IsTrueOrErr(ok, err) {
		return ok, err
	}

	if ok, err := ver.verTrueEqualFactMainLogic(stmt, state, checkRequirements); IsTrueOrErr(ok, err) {
		return ok, err
	}

	if ok, err := ver.verByReplaceFcInSpecFactWithValueAndCompute(stmt, state); IsTrueOrErr(ok, err) {
		return ok, err
	}

	return false, nil
}

func (ver *Verifier) verTrueEqualFactMainLogic(stmt *ast.SpecFactStmt, state *VerState, checkRequirements bool) (bool, error) {
	var ok bool
	var err error

	if checkRequirements && !state.ReqOk {
		// REMARK: 这里 state 更新了： ReqOk 更新到了 true
		if ok, state, err = ver.checkFnsReqAndUpdateReqState(stmt, state); IsFalseOrErr(ok, err) {
			return ok, err
		}

		if !isValidEqualFact(stmt) {
			return false, fmt.Errorf("invalid equal fact: %s", stmt)
		}
	}

	if ok, err := ver.verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(stmt.Params[0], stmt.Params[1], state); IsTrueOrErr(ok, err) {
		return ok, err
	}

	if leftAsFn, ok := stmt.Params[0].(*ast.FcFn); ok {
		if rightAsFn, ok := stmt.Params[1].(*ast.FcFn); ok {
			ret := ver.verTrueEqualFact_FcFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if ret.IsErr() {
				return false, ret.Err
			}
			if ret.IsOk() {
				return true, nil
			}
		}
	} else {
		return false, nil
	}

	return false, nil
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && string(stmt.PropName) == glob.KeySymbolEqual
}

func (ver *Verifier) verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	if ok, err := ver.verEqualBuiltin(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verEqualSpecMem(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if !state.isFinalRound() {
		if ok, err := ver.verLogicMem_leftToRight_RightToLeft(left, right, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}

		if ok, err := ver.verEqualUniMem(left, right, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verEqualBuiltin(left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	ok, msg, err := cmp.CmpBy_Literally_NumLit_PolynomialArith(left, right) // 完全一样
	if err != nil {
		return false, err
	}
	if ok {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), msg)
		}
		return true, nil
	}

	// 如果是 fn 那就层层盘剥
	nextState := state.GetNoMsg()
	if ok, _, err := ver.decomposeFcFnsAndCheckEquality(left, right, nextState, ver.verEqualBuiltin); err != nil {
		return false, err
	} else if ok {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), "each item of %s and %s are equal correspondingly")
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) verEqualSpecMem(left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	// if ver.env.CurMatchProp == nil {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		ok, err := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	nextState := state.GetNoMsg()

	ok, msg, err := ver.getEqualFcsAndCmpOneByOne(curEnv, left, right, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		if state.WithMsg {
			ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), msg)
		}
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) verLogicMem_leftToRight_RightToLeft(left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	equalFact := ast.NewEqualFact(left, right)
	ok, err := ver.verSpecFactLogicMem(equalFact, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return false, err
	}
	ok, err = ver.verSpecFactLogicMem(equalFactParamReversed, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) verEqualUniMem(left ast.Fc, right ast.Fc, state *VerState) (bool, error) {
	equalFact := ast.NewEqualFact(left, right)
	ok, err := ver.verSpecFact_UniMem(equalFact, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	equalFactParamReversed, err := equalFact.ReverseSpecFactParamsOrder()
	if err != nil {
		return false, err
	}
	ok, err = ver.verSpecFact_UniMem(equalFactParamReversed, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) getEqualFcsAndCmpOneByOne(curEnv *env.Env, left ast.Fc, right ast.Fc, state *VerState) (bool, string, error) {
	var equalToLeftFcs, equalToRightFcs *[]ast.Fc
	var gotLeftEqualFcs, gotRightEqualFcs bool

	equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
	equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

	if gotLeftEqualFcs && gotRightEqualFcs {
		if equalToLeftFcs == equalToRightFcs {
			return true, fmt.Sprintf("%s = %s, by either their equality is known, or it is ensured by transitivity of equality.", left, right), nil
		}
	}

	if ok, msg, err := ver.cmpFc_Builtin_Then_Decompose_Spec(left, right, state); err != nil {
		return false, "", err
	} else if ok {
		return true, msg, nil
	}

	if gotLeftEqualFcs {
		for _, equalToLeftFc := range *equalToLeftFcs {
			if ok, _, err := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToLeftFc, right, state); err != nil {
				return false, "", err
			} else if ok {
				return true, fmt.Sprintf("It is true that:\n%s = %s and %s = %s", equalToLeftFc, right, equalToLeftFc, left), nil
			}
		}
	}

	if gotRightEqualFcs {
		for _, equalToRightFc := range *equalToRightFcs {
			if ok, _, err := ver.cmpFc_Builtin_Then_Decompose_Spec(equalToRightFc, left, state); err != nil {
				return false, "", err
			} else if ok {
				return true, fmt.Sprintf("It is true that\n%s = %s and %s = %s", left, equalToRightFc, equalToRightFc, right), nil
			}
		}
	}

	return false, "", nil
}

func (ver *Verifier) decomposeFcFnsAndCheckEquality(left ast.Fc, right ast.Fc, state *VerState, verifyFunc func(left ast.Fc, right ast.Fc, state *VerState) (bool, error)) (bool, string, error) {
	if leftAsFn, ok := left.(*ast.FcFn); ok {
		if rightAsFn, ok := right.(*ast.FcFn); ok {
			if len(leftAsFn.Params) != len(rightAsFn.Params) {
				return false, "", nil
			}

			// compare head
			ok, err := verifyFunc(leftAsFn.FnHead, rightAsFn.FnHead, state)
			if err != nil {
				return false, "", err
			}
			if !ok {
				return false, "", nil
			}
			// compare params
			for i := range leftAsFn.Params {
				ok, err := verifyFunc(leftAsFn.Params[i], rightAsFn.Params[i], state)
				if err != nil {
					return false, "", err
				}
				if !ok {
					return false, "", nil
				}
			}

			return true, fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right), nil
		}
	}
	return false, "", nil
}
