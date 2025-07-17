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
	cmp "golitex/cmp"
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

// SERIOUS BUG
// WARNING
// REMARK
// TODO: cmpFc, fcFnEq, fcEqualSpec 大循环本质上是有问题的，会有循环论证的风险：know p(p(1,2), 0) = 1, 则现在问 p(1,2) =1 吗？我会比较 p(1,2) = p(p(1,2), 0)，那这时候就出问题了：我因为一位位地比，所以又回到了比较 1 = p(1,2)
func (ver *Verifier) cmpFc(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	ok, msg, err := cmp.Cmp_ByBIR(left, right) // 完全一样
	if err != nil {
		return false, err
	}
	if ok {
		return ver.equalTrueAddSuccessMsg(left, right, state, msg)
	}

	if ok {
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
					ver.successWithMsg(fmt.Sprintf("known %s = %s", left, right), "")
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
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToLeftFc, right, equalToLeftFc, left), "")
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
						ver.successWithMsg(fmt.Sprintf("known:\n%s = %s\n%s = %s", equalToRightFc, left, equalToRightFc, right), "")
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

	// REMARK: 必须先比头部，再比较params。否则 know (1,2)[0] = 1后，我要比较 (1,2) = 1，这时候会死循环：因为 1 = (1,2)[0]，所以 (1,2) 会被拿来和 (1,2)[0] 比较，然后因为是先比params再比头部，所以会先运行 1 和 (1,2) 比较，则死循环.
	ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	if err != nil {
		return false, err
	}
	if !ok {
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

	return true, nil
}

func (ver *Verifier) verTrueEqualFact_FcFnEqual_NoCheckRequirements(left, right *ast.FcFn, state VerState) (bool, error) {
	var ok bool
	var err error

	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	ok, err = ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.FnHead, right.FnHead}), state, false)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)

		ok, err := ver.verTrueEqualFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left.Params[i], right.Params[i]}), state, false)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
