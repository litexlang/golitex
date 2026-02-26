// Copyright Jiachen Shen.
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
)

func (ver *Verifier) ReplaceObjsInSpecFactWithValue(fact ast.SpecificFactStmt) (bool, ast.SpecificFactStmt) {
	switch fact := fact.(type) {
	case *ast.PureSpecificFactStmt:
		newParams := make([]ast.Obj, len(fact.Params))
		replaced := false
		for i, param := range fact.Params {
			replacedByEval, newObj := ver.GetValueOfSymbol(param)
			if replacedByEval {
				replaced = true
				newParams[i] = newObj
			} else {
				newParams[i] = param
			}
		}
		return replaced, ast.NewPureSpecificFactStmt(fact.IsTrue, fact.PropName, newParams, fact.Line)
	case *ast.ExistSpecificFactStmt:
		return false, fact
	}

	return false, nil
}

func (ver *Verifier) verByReplaceObjInSpecFactWithValue(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewUnknownVerRet(stmt)
	}

	replaced, newStmt := ver.ReplaceObjsInSpecFactWithValue(asStmt)

	if replaced {
		verRet := ver.verTrueEqualWholeProcess(newStmt.(*ast.PureSpecificFactStmt), state.CopyAndReqOkToFalse())
		if verRet.IsErr() {
			return ast.NewErrVerRet(stmt).AddExtraInfo("failed to verify true equal fact: " + verRet.String())
		}

		if verRet.IsTrue() {
			msg := fmt.Sprintf("replacing the symbols with their values:\n%s", newStmt.String())
			if state.WithMsg {
				return ast.NewTrueVerRet(stmt, nil, msg)
			}
			return ast.NewTrueVerRet(stmt, nil, "")
		}
	}

	return ast.NewUnknownVerRet(stmt).AddExtraInfo(fmt.Sprintf("%s is not equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String()))
}
