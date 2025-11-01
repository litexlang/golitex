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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verEnumStmt(stmt *ast.EnumStmt, state *VerState) VerRet {
	if verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.CurSet, ast.FcAtom(glob.KeywordFiniteSet)}, stmt.Line), state); verRet.IsErr() {
		return verRet
	} else if verRet.IsTrue() {
		if verRet := ver.lenIsZeroThenEnumIsEmpty(stmt, state); verRet.IsTrue() {
			return verRet
		}
	}

	if verRet := ver.forallObjNotInSetThenTheSetIsEmpty(stmt, state); verRet.IsTrue() {
		return verRet
	}

	forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts := ast.TransformEnumToUniFact(stmt.CurSet, stmt.Items)

	verRet := ver.VerFactStmt(forallItemInSetEqualToOneOfGivenItems, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	for _, domFact := range pairwiseNotEqualFacts {
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	for _, equalFact := range itemsInSetFacts {
		verRet := ver.VerFactStmt(equalFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	return NewVerTrue("")
}

func (ver *Verifier) lenIsZeroThenEnumIsEmpty(stmt *ast.EnumStmt, state *VerState) VerRet {
	lenOverStmtName := ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.CurSet})
	equalFact := ast.EqualFact(lenOverStmtName, ast.FcAtom("0"))
	verRet := ver.VerFactStmt(equalFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("len(%s) = 0 is equivalent to %s", stmt.CurSet, stmt))
	}

	return NewVerTrue("")
}

func (ver *Verifier) forallObjNotInSetThenTheSetIsEmpty(stmt *ast.EnumStmt, state *VerState) VerRet {
	if len(stmt.Items) != 0 {
		return NewVerUnknown("")
	}

	allObjectsNotInSetThenSetIsEmpty := ast.NewUniFact([]string{"x"}, []ast.Fc{ast.FcAtom(glob.KeywordObj)}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{ast.FcAtom("x"), stmt.CurSet}, stmt.Line)}, stmt.Line)
	verRet := ver.VerFactStmt(allObjectsNotInSetThenSetIsEmpty, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	if state.WithMsg {
		ver.successWithMsg(stmt.String(), fmt.Sprintf("builtin rule:\n%s\nis equivalent to\n%s", allObjectsNotInSetThenSetIsEmpty, stmt))
	}

	return NewVerTrue("")
}
