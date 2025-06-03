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
	glob "golitex/glob"
)

// 暂时先不考虑 fn_commutative, fn_associative 的情况
func (ver *Verifier) verEqualFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !isValidEqualFact(stmt) {
		return false, fmt.Errorf("invalid equal fact: %v", stmt)
	}

	return ver.verFcEqual(stmt.Params[0], stmt.Params[1], state)
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
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		// TODO: 这里还要用 MatchEnv 实现一下

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
	}
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
