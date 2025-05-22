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
	ast "golitex/ast"
)

func (ver *Verifier) verSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if ok, err := ver.isValidSpecFact(stmt); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.isSpecFactCommutative(stmt); err != nil {
		return false, err
	} else if ok {
		return ver.verSpecFactStepByStep(stmt, state)
	} else {
		if ok, err := ver.verSpecFactStepByStep(stmt, state); err != nil {
			return false, err
		} else if ok {
			return true, nil
		} else {
			paramReversedStmt, err := stmt.ReverseSpecFactParamsOrder()
			if err != nil {
				return false, err
			}
			return ver.verSpecFactStepByStep(paramReversedStmt, state)
		}
	}
}

func (ver *Verifier) isValidSpecFact(stmt *ast.SpecFactStmt) (bool, error) {
	return true, nil
}

func (ver *Verifier) isSpecFactCommutative(stmt *ast.SpecFactStmt) (bool, error) {
	return false, nil
}

func (ver *Verifier) verSpecFactStepByStep(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	return false, nil
}
