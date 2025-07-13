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

func (ver *Verifier) verEnumStmt(stmt *ast.EnumStmt, state VerState) (bool, error) {
	if ok, err := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.CurSet, ast.FcAtom(glob.KeywordFiniteSet)}), state); err != nil || ok {
		if err != nil {
			return false, err
		}
		if ok, _ := ver.lenIsZeroThenEnumIsEmpty(stmt, state); ok {
			return true, nil
		}
	}

	if ok, _ := ver.forallObjNotInSetThenTheSetIsEmpty(stmt, state); ok {
		return true, nil
	}

	forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts := ast.TransformEnumToUniFact(stmt.CurSet, stmt.Items)

	ok, err := ver.VerFactStmt(forallItemInSetEqualToOneOfGivenItems, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	for _, domFact := range pairwiseNotEqualFacts {
		ok, err := ver.VerFactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, equalFact := range itemsInSetFacts {
		ok, err := ver.VerFactStmt(equalFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) lenIsZeroThenEnumIsEmpty(stmt *ast.EnumStmt, state VerState) (bool, error) {
	lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.CurSet})
	equalFact := ast.EqualFact(lenOverStmtName, ast.FcAtom("0"))
	ok, err := ver.VerFactStmt(equalFact, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("len(%s) = 0 is equivalent to %s", stmt.CurSet, stmt))
	}

	return true, nil
}

func (ver *Verifier) forallObjNotInSetThenTheSetIsEmpty(stmt *ast.EnumStmt, state VerState) (bool, error) {
	if len(stmt.Items) != 0 {
		return false, nil
	}

	allObjectsNotInSetThenSetIsEmpty := ast.NewUniFact([]string{"x"}, []ast.Fc{ast.FcAtom(glob.KeywordObj)}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{ast.FcAtom("x"), stmt.CurSet})})
	ok, err := ver.VerFactStmt(allObjectsNotInSetThenSetIsEmpty, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("builtin rule:\n%s\nis equivalent to\n%s", allObjectsNotInSetThenSetIsEmpty, stmt))
	}

	return true, nil
}
