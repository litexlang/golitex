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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) verTrueEqualFactAndCheckFnReq(stmt *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	nextState := state.CopyAndReqOkToTrue()
	if !state.ReqOk {
		if verRet := ver.checkFnsReqInSpecFact(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if verRet := ver.verTrueEqualWholeProcess(stmt, nextState); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return ast.NewUnknownVerRet(stmt)
}

func (ver *Verifier) verTrueEqualWholeProcess(stmt *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	if len(stmt.Params) != 2 {
		return ast.NewEmptyUnknownVerRet()
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

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verTrueEqualPreProcess(stmt *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	if verRet := cmp.CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(stmt.Params[0], stmt.Params[1]); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	if leftAsInstSetTemplate, ok := stmt.Params[0].(*ast.InstSetTemplateObj); ok {
		if rightAsFnSetObjWithName, ok := stmt.Params[1].(*ast.FnSetObjWithName); ok {
			def := ver.Env.GetSetTemplateDef(string(leftAsInstSetTemplate.Name))
			if def == nil {
				return ast.NewEmptyUnknownVerRet()
			}
			if len(leftAsInstSetTemplate.Params) != len(def.Params) {
				return ast.NewEmptyUnknownVerRet()
			}
			uniMap := make(map[string]ast.Obj)
			for i, param := range def.Params {
				uniMap[param] = leftAsInstSetTemplate.Params[i]
			}
			equalTo, err := def.EqualTo.Instantiate(uniMap)
			if err != nil {
				return ast.NewEmptyUnknownVerRet()
			}
			equality := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{rightAsFnSetObjWithName, equalTo}, glob.BuiltinLine0)

			verRet := ver.verTrueEqualFactAndCheckFnReq(equality, state.CopyAndReqOkToTrue())

			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		} else if rightAsFnSetObjWithoutName, ok := stmt.Params[1].(*ast.FnSetObjWithoutName); ok {
			def := ver.Env.GetSetTemplateDef(string(leftAsInstSetTemplate.Name))
			if def == nil {
				return ast.NewEmptyUnknownVerRet()
			}
			if len(leftAsInstSetTemplate.Params) != len(def.Params) {
				return ast.NewEmptyUnknownVerRet()
			}
			uniMap := make(map[string]ast.Obj)
			for i, param := range def.Params {
				uniMap[param] = leftAsInstSetTemplate.Params[i]
			}
			equalTo, err := def.EqualTo.Instantiate(uniMap)
			if err != nil {
				return ast.NewEmptyUnknownVerRet()
			}
			verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{rightAsFnSetObjWithoutName, equalTo}, glob.BuiltinLine0), state.CopyAndReqOkToTrue())
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	}

	return ver.verByReplaceObjInSpecFactWithValue(stmt, state)
}

func (ver *Verifier) verTrueEqualMainProcess(stmt *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	left := stmt.Params[0]
	right := stmt.Params[1]

	if verRet := ver.verEqualMainProcessByBuiltinRules(left, right, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verEqualBySpecMem(left, right); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verEqualUniMem(left, right, state); verRet.IsErr() {
			return verRet
		} else if verRet.IsTrue() {
			return verRet
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verTrueEqualPostProcess(stmt *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	return ver.verObjsEqualByTheyAreFnObjsAndTheirHeadsAndParamsAreEqual(stmt.Params[0], stmt.Params[1], state)
}

func (ver *Verifier) verObjsEqualByTheyAreFnObjsAndTheirHeadsAndParamsAreEqual(left, right ast.Obj, state *VerState) ast.VerRet {
	if leftAsFn, ok := left.(*ast.FnObj); ok {
		if rightAsFn, ok := right.(*ast.FnObj); ok {
			verRet := ver.verTrueEqualFact_ObjFnEqual_NoCheckRequirements(leftAsFn, rightAsFn, state)
			if verRet.IsErr() || verRet.IsTrue() {
				return verRet
			}
		}
	}
	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verTrueEqualFact_ObjFnEqual_NoCheckRequirements(left, right *ast.FnObj, state *VerState) ast.VerRet {
	if len(left.Params) != len(right.Params) {
		return ast.NewEmptyUnknownVerRet()
	}

	// ok, err = ver.fcEqualSpec(left.FnHead, right.FnHead, state)
	verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.FnHead, right.FnHead}, glob.BuiltinLine0), state.CopyAndReqOkToTrue())
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	for i := range left.Params {
		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left.Params[i], right.Params[i]}, glob.BuiltinLine0), state.CopyAndReqOkToTrue())
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	equalFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, right}, glob.BuiltinLine0)
	return ast.NewTrueVerRet(equalFact, nil, fmt.Sprintf("headers and parameters of %s and %s are equal correspondingly", left, right))
}
