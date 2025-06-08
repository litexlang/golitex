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
// Litex discord server: https://discord.gg/uvrHM7eS
// Litex zulip chat: https://litex.zulipchat.com/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	env "golitex/environment"
	glob "golitex/glob"
)

// 暂时先不考虑 fn_commutative, fn_associative 的情况
func (ver *Verifier) verEqualFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.isValidSpecFact_EqualFact(stmt); err != nil {
		return false, err
	} else if !ok {
		return false, nil
	}

	if !isValidEqualFact(stmt) {
		return false, fmt.Errorf("invalid equal fact: %v", stmt)
	}

	ok, err := ver.verFcEqual(stmt.Params[0], stmt.Params[1], state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if leftAsFn, ok := stmt.Params[0].(*ast.FcFn); ok {
		if rightAsFn, ok := stmt.Params[1].(*ast.FcFn); ok {
			fnNameEqual, err := ver.verFcEqual(leftAsFn.FnHead, rightAsFn.FnHead, state)
			if err != nil {
				return false, err
			}
			if fnNameEqual {
				if len(leftAsFn.ParamSegs) != len(rightAsFn.ParamSegs) {
					return false, nil
				}

				for i := range leftAsFn.ParamSegs {
					ok, err := ver.verFcEqual(leftAsFn.ParamSegs[i], rightAsFn.ParamSegs[i], state)
					if err != nil {
						return false, err
					}
					if !ok {
						return false, nil
					}
				}
				return true, nil
			} else {
				return false, nil
			}
		} else {
			return false, nil
		}
	} else {
		return false, nil
	}
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && stmt.PropName.Name == glob.KeySymbolEqual
}

func (ver *Verifier) verFcEqual(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	if ok, err := ver.verEqualBuiltin(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verEqualSpecMem(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	} else {
		// 如果 ver.CurMatchEnv 存在，那还要用specMem来验证
		if ver.env.CurMatchProp != nil {
			equalFact := ver.makeEqualFact(left, right)
			ok, err := ver.verSpecFact_SpecMem(equalFact, state)
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}
		}
	}

	if ok, err := ver.verEqualSpecMemAndLogicMem(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if !state.isFinalRound() {
		if ok, err := ver.verEqualUniMem(left, right, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verEqualBuiltin(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	ok, err := cmp.CmpUsingBuiltinRule(left, right) // 完全一样
	if err != nil {
		return false, err
	}
	if ok {
		return ver.equalTrueAddSuccessMsg(left, right, state, "builtin rules")
	}
	return false, nil
}

func (ver *Verifier) verEqualSpecMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	if ver.env.CurMatchProp == nil {
		for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
			ok, err := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}
		}
	} else {
		for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
			ok, err := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
			if err != nil {
				return false, err
			}
			if ok {
				return true, nil
			}

			ok, err = ver.equalFact_MatchEnv_SpecMem_atEnv(curEnv, left, right, state)
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

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	var equalToLeftFcs, equalToRightFcs *[]ast.Fc
	var gotLeftEqualFcs, gotRightEqualFcs bool

	equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
	equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

	if gotLeftEqualFcs && gotRightEqualFcs {
		if equalToLeftFcs == equalToRightFcs {
			return ver.equalTrueAddSuccessMsg(left, right, state, "known")
		}
	}

	if gotLeftEqualFcs {
		for _, equalToLeftFc := range *equalToLeftFcs {
			if ok, err := ver.cmpFc(equalToLeftFc, right, state); err != nil {
				return false, err
			} else if ok {
				return ver.equalTrueAddSuccessMsg(left, right, state, "known")
			}
		}
	}

	if gotRightEqualFcs {
		for _, equalToRightFc := range *equalToRightFcs {
			if ok, err := ver.cmpFc(equalToRightFc, left, state); err != nil {
				return false, err
			} else if ok {
				return ver.equalTrueAddSuccessMsg(left, right, state, "known")
			}
		}
	}

	return false, nil
}

func (ver *Verifier) equalFact_MatchEnv_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	_ = curEnv
	_ = left
	_ = right
	_ = state
	return false, nil
}

func (ver *Verifier) verEqualSpecMemAndLogicMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	equalFact := ver.makeEqualFact(left, right)
	ok, err := ver.verSpecFactSpecMemAndLogicMem(equalFact, state)
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
	ok, err = ver.verSpecFactSpecMemAndLogicMem(equalFactParamReversed, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) verEqualUniMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	equalFact := ver.makeEqualFact(left, right)
	ok, err := ver.verSpecFactUniMem(equalFact, state)
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
	ok, err = ver.verSpecFactUniMem(equalFactParamReversed, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}
