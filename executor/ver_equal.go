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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verTrueEqualFactAndCheckFnReq2(stmt *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	if verRet := ver.verTrueEqualWholeProcess(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualWholeProcess(stmt *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	if len(stmt.Params) != 2 {
		return glob.NewEmptyVerRetUnknown()
	}

	verRet := ver.verTrueEqualPreProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verTrueEqualMainProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verTrueEqualPostProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualPreProcess(stmt *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	return ver.verByReplaceObjInSpecFactWithValue(stmt, state)
}

func (ver *Verifier) verTrueEqualMainProcess(stmt *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	left := stmt.Params[0]
	right := stmt.Params[1]

	if verRet := ver.verEqualBuiltin(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualSpecMem(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verEqualUniMem(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualPostProcess(stmt *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	return ver.verObjsEqualByTheyAreFnObjsAndTheirHeadsAndParamsAreEqual(stmt.Params[0], stmt.Params[1], state)
}

func (ver *Verifier) verObjsEqualByTheyAreFnObjsAndTheirHeadsAndParamsAreEqual(left, right ast.Obj, state *VerState) *glob.VerRet {
	if leftAsFn, ok := left.(*ast.FnObj); ok {
		if rightAsFn, ok := right.(*ast.FnObj); ok {
			verRet := ver.verTrueEqualFact_ObjFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verTrueEqualFact_ObjFnEqual_NoCheckRequirements(left, right *ast.FnObj, state *VerState) *glob.VerRet {
	if len(left.Params) != len(right.Params) {
		return glob.NewEmptyVerRetUnknown()
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	verRet := ver.verTrueEqualFactAndCheckFnReq2(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.FnHead, right.FnHead}, glob.BuiltinLine0), state.CopyAndReqOkToTrue())
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyVerRetUnknown()
	}

	for i := range left.Params {
		// ok, err := ver.fcEqualSpec(left.Params[i], right.Params[i], state)

		verRet := ver.verTrueEqualFactAndCheckFnReq2(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.Params[i], right.Params[i]}, glob.BuiltinLine0), state.CopyAndReqOkToTrue())
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	// return newTrueVerRet("")
	return glob.NewEmptyVerRetTrue()
}
