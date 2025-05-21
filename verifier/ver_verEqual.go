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

func (ver *Verifier) verEqual(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if !isValidEqualFact(stmt) {
		return false, fmt.Errorf("invalid equal fact: %v", stmt)
	}

	return ver.verEqualSwap(stmt, state)
}

func isValidEqualFact(stmt *ast.SpecFactStmt) bool {
	return len(stmt.Params) == 2 && stmt.PropName.Name == glob.KeySymbolEqual
}

func (ver *Verifier) verEqualSwap(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	stmtWithReversedParamOrder, err := stmt.ReverseSpecFactParamsOrder()
	if err != nil {
		return false, err
	}

	statements := []*ast.SpecFactStmt{stmt, stmtWithReversedParamOrder}

	for _, s := range statements {
		ok, err := ver.verEqualLeftToRight(s.Params[0], s.Params[1], state)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}

func (ver *Verifier) verEqualLeftToRight(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	if ok, err := verEqualBuiltin(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verEqualSpecMem(left, right, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func verEqualBuiltin(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	ok, err := cmp.CmpFcRule(left, right) // 完全一样
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}
	return false, nil
}

func (ver *Verifier) verEqualSpecMem(left ast.Fc, right ast.Fc, state VerState) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		var equalToLeftFcs, equalTorightFcs *[]ast.Fc
		var gotLeftEqualFcs, gotRightEqualFcs bool

		equalToLeftFcs, gotLeftEqualFcs = curEnv.GetEqualFcs(left)
		equalTorightFcs, gotRightEqualFcs = curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalTorightFcs {
				return ver.eqaulTrueAddSuccessMsg(left, right, state, "known")
			}
		}

		if gotLeftEqualFcs {
			for _, equalToLeftFc := range *equalToLeftFcs {
				if ok, err := ver.cmpFc(equalToLeftFc, right, state); err != nil {
					return false, err
				} else if ok {
					return ver.eqaulTrueAddSuccessMsg(left, right, state, "known")
				}
			}
		}

		if gotRightEqualFcs {
			for _, equalToRightFc := range *equalTorightFcs {
				if ok, err := ver.cmpFc(equalToRightFc, left, state); err != nil {
					return false, err
				} else if ok {
					return ver.eqaulTrueAddSuccessMsg(left, right, state, "known")
				}
			}
		}
	}
	return false, nil
}
