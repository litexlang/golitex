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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) isEqualFact_Check(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !stmt.IsTrue() {
		return false, nil
	}

	if ok, err := stmt.IsValidEqualFact(); err != nil {
		return false, err
	} else if !ok {
		return false, nil
	}

	return ver.fcEqualSpec(stmt.Params[0], stmt.Params[1], state)
}

func (ver *Verifier) cmpFc(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	ok, err := ver.fcEqual_Commutative_Associative_CmpRule(left, right, state)
	if err != nil {
		return false, err
	}
	if ok {
		// isSuccess = true
		return true, nil
	}

	leftAsFn, ok := left.(*ast.FcFn)
	if ok {
		rightAsFn, ok := right.(*ast.FcFn)
		if ok {
			ok, err = ver.fcFnEq(leftAsFn, rightAsFn, state.toFinalRound())
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}
		}
	}

	return false, nil
}

// Iterate over all equal facts. On each equal fact, use commutative, associative, cmp rule to compare.
func (ver *Verifier) fcEqualSpec(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	if ok, err := ver.cmpFc(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		var equalToLeftFcs, equalToRightFcs *[]ast.Fc
		var gotLeftEqualFcs, gotRightEqualFcs bool

		equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
		equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalToRightFcs {
				if state.requireMsg() {
					ver.successWithMsg(fmt.Sprintf("known %s = %s", left.String(), right.String()), "")
				}
				return true, nil
			}
		}

		if gotLeftEqualFcs {
			rightAsStr := right.String()
			for _, equalToLeftFc := range *equalToLeftFcs {
				if equalToLeftFc.String() == rightAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if ok, err := ver.cmpFc(equalToLeftFc, right, state); err != nil {
					return false, err
				} else if ok {
					if state.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftFc.String(), right.String(), equalToLeftFc.String(), left.String()), "")
					}
					return true, nil
				}
			}
		}

		if gotRightEqualFcs {
			leftAsStr := left.String()
			for _, equalToRightFc := range *equalToRightFcs {
				if equalToRightFc.String() == leftAsStr { // 最一开头已经比较过，这里不需要再比较了
					continue
				}

				if ok, err := ver.cmpFc(equalToRightFc, left, state); err != nil {
					return false, err
				} else if ok {
					if state.requireMsg() {
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightFc.String(), left.String(), equalToRightFc.String(), right.String()), "")
					}
					return true, nil
				}
			}
		}
	}

	return false, nil
}

func (ver *Verifier) fcFnEq(left, right *ast.FcFn, state VerState) (bool, error) {
	var ok bool
	var err error
	state = state.addRound()

	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	for i := range left.Params {
		ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)
		// ok, err := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.Params[i], right.Params[i]}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	// ok, err = ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.FnHead, right.FnHead}), state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) verTrueEqualFact_FcFnEqual(left, right *ast.FcFn, state VerState) (bool, error) {
	var ok bool
	var err error
	state = state.addRound()

	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	ok, err = ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.FnHead, right.FnHead}), state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)
		ok, err := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.Params[i], right.Params[i]}), state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
