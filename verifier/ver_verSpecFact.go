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
	glob "golitex/glob"
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
	if ok, err := ver.verSpecialSpecFact(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFactUseDefinition(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFactSpecMemAndLogicMem(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	if ok, err := ver.verSpecFactUniMem(stmt, state); err != nil {
		return false, err
	} else if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) verSpecialSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.NameIs(glob.KeywordInduction) {
		return ver.mathInductionFact(stmt, state)
	}

	if stmt.NameIs(glob.KeywordCommutativeFn) {
		return ver.commutativeFnByDef(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFact(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqual) {
		return ver.isFnEqualFact_Check(stmt, state)
	}

	if stmt.NameIs(glob.KeySymbolEqualEqualEqual) {
		return ver.isEqualFact_Check(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) verSpecFactUseDefinition(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsPureFact() {
		return ver.specFactProveByDefinition(stmt, state)
	}

	if stmt.IsExist_St_Fact() {
		return ver.useExistPropDefProveExist_St(stmt, state)
	}

	return false, nil
}

func (ver *Verifier) verSpecFactSpecMemAndLogicMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	return ver.specFactUsingMemSpecifically(stmt, state)
}

func (ver *Verifier) verSpecFactUniMem(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	return ver.SpecFactUni(stmt, state)
}
