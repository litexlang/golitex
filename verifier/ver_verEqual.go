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
	env "golitex/environment"
	glob "golitex/glob"
)

// how equality is verified is different from other facts because 1. it is stored differently 2. its transitive and commutative property is automatically used by the verifier
func (ver *Verifier) verTrueEqualFact(stmt *ast.SpecFactStmt, state VerState, checkRequirements bool) (bool, error) {
	if checkRequirements {
		if ok, err := ver.checkSpecFactRequirements(stmt, state); err != nil {
			return false, err
		} else if !ok {
			return false, nil
		}

		if !isValidEqualFact(stmt) {
			return false, fmt.Errorf("invalid equal fact: %v", stmt)
		}
	}

	ok, err := ver.verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(stmt.Params[0], stmt.Params[1], state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if leftAsFn, ok := stmt.Params[0].(*ast.FcFn); ok {
		if rightAsFn, ok := stmt.Params[1].(*ast.FcFn); ok {
			ok, err := ver.verTrueEqualFact_FcFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if err != nil {
				return false, err
			}
			if ok {
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

func (ver *Verifier) verFcEqual_ByBtRules_SpecMem_LogicMem_UniMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
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
	ok, msg, err := cmp.Cmp_ByBIR(left, right) // 完全一样
	if err != nil {
		return false, err
	}
	if ok {
		return ver.equalTrueAddSuccessMsg(left, right, state, msg)
	}
	return false, nil
}

func (ver *Verifier) verEqualSpecMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
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
	// } else {
	// 	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
	// 		ok, err := ver.equalFact_SpecMem_atEnv(curEnv, left, right, state)
	// 		if err != nil {
	// 			return false, err
	// 		}
	// 		if ok {
	// 			return true, nil
	// 		}

	// 		ok, err = ver.equalFact_MatchEnv_SpecMem_atEnv(curEnv, left, right, state)
	// 		if err != nil {
	// 			return false, err
	// 		}
	// 		if ok {
	// 			return true, nil
	// 		}
	// 	}
	// }
	return false, nil
}

func (ver *Verifier) equalFact_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	var equalToLeftFcs, equalToRightFcs *[]ast.Fc
	var gotLeftEqualFcs, gotRightEqualFcs bool

	equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
	equalToRightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

	if gotLeftEqualFcs && gotRightEqualFcs {
		if equalToLeftFcs == equalToRightFcs {
			return ver.equalTrueAddSuccessMsg(left, right, state, fmt.Sprintf("known fact:\n%s = %s", left.String(), right.String()))
		}
	}

	if gotLeftEqualFcs {
		for _, equalToLeftFc := range *equalToLeftFcs {
			if ok, err := ver.cmpFc(equalToLeftFc, right, state); err != nil {
				return false, err
			} else if ok {
				return ver.equalTrueAddSuccessMsg(left, right, state, fmt.Sprintf("known fact:\n%s = %s", left.String(), right.String()))
			}
		}
	}

	if gotRightEqualFcs {
		for _, equalToRightFc := range *equalToRightFcs {
			if ok, err := ver.cmpFc(equalToRightFc, left, state); err != nil {
				return false, err
			} else if ok {
				return ver.equalTrueAddSuccessMsg(left, right, state, fmt.Sprintf("known fact:\n%s = %s", left.String(), right.String()))
			}
		}
	}

	return false, nil
}

// func (ver *Verifier) equalFact_MatchEnv_SpecMem_atEnv(curEnv *env.Env, left ast.Fc, right ast.Fc, state VerState) (bool, error) {
// 	// panic("equalFact_MatchEnv_SpecMem_atEnv: not implemented")
// 	equalFact := ver.makeEqualFact(left, right)
// 	return ver.specFact_MatchEnv_SpecMem(curEnv, equalFact, state)
// }

func (ver *Verifier) verEqualSpecMemAndLogicMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	equalFact := ver.makeEqualFact(left, right)
	ok, err := ver.verSpecFact_SpecMemAndLogicMem(equalFact, state)
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
	ok, err = ver.verSpecFact_SpecMemAndLogicMem(equalFactParamReversed, state)
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
