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

func (ver *Verifier) verEnumStmt(stmt *ast.EnumStmt, state *VerState) ExecRet {
	if verRet := ver.VerFactStmt(ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{stmt.CurSet, ast.Atom(glob.KeywordFiniteSet)}, stmt.Line), state); verRet.IsErr() {
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

	return NewExecTrue("")
}

func (ver *Verifier) lenIsZeroThenEnumIsEmpty(stmt *ast.EnumStmt, state *VerState) ExecRet {
	lenOverStmtName := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{stmt.CurSet})
	equalFact := ast.EqualFact(lenOverStmtName, ast.Atom("0"))
	verRet := ver.VerFactStmt(equalFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	msg := fmt.Sprintf("len(%s) = 0 is equivalent to %s", stmt.CurSet, stmt)
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}

func (ver *Verifier) forallObjNotInSetThenTheSetIsEmpty(stmt *ast.EnumStmt, state *VerState) ExecRet {
	if len(stmt.Items) != 0 {
		return NewExecUnknown("")
	}

	allObjectsNotInSetThenSetIsEmpty := ast.NewUniFact([]string{"x"}, []ast.Obj{ast.Atom(glob.KeywordObj)}, []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("x"), stmt.CurSet}, stmt.Line)}, stmt.Line)
	verRet := ver.VerFactStmt(allObjectsNotInSetThenSetIsEmpty, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	msg := fmt.Sprintf("builtin rule:\n%s\nis equivalent to\n%s", allObjectsNotInSetThenSetIsEmpty, stmt)
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecTrue(""))
}
