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

func (ver *Verifier) verSpecFactByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if stmt.NameIs(glob.KeywordIn) {
		return ver.inFactBuiltinRules(stmt, state)
	} else if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TrueExist_St {
		return ver.trueExistInSt(stmt, state)
	}

	if stmt.NameIs(glob.KeywordEqualTuple) {
		return ver.verEqualTupleByBuiltinRules(stmt, state)
	}

	if verRet := ver.verNumberLogicRelaOpt_BuiltinRules(stmt, state); verRet.IsErr() {
		return verRet
	} else if verRet.IsTrue() {
		return verRet
	}

	if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure {
		return ver.verNotTrueEqualFact_BuiltinRules_WithState(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIsCart) && stmt.TypeEnum == ast.TruePure {
		return ver.verIsCartByBuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TruePure {
		return ver.verItemExistsInByBuiltinRules(stmt, state)
	}

	if verRet := ver.IsInNonEmptyByBuiltinRules(stmt, state); verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verNumberLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if !stmt.IsTrue() {
		return NewEmptyExecUnknown()
	}

	verRet := ver.btNumberInfixCompareProp(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return NewEmptyExecUnknown()
	}

	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		return NewEmptyExecUnknown()
	}

	rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if !ok {
		return NewEmptyExecUnknown()
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "builtin rules", NewEmptyExecTrue())
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) btLitNumInNatOrIntOrRatOrRealOrComplex(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	_ = state

	if stmt.PropName != glob.KeywordIn {
		return NewEmptyExecUnknown()
	}

	// Note: Messages should be handled by the caller, not in defer functions
	isSuccess := false
	defer func() {
		_ = isSuccess
	}()

	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftFc, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftFc)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftFc)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftFc)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftFc)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftFc)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verItemExistsInByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 1 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 1 param, but got %d", len(stmt.Params)))
	}

	if ast.IsEnumSetObj(stmt.Params[0]) {
		asEnumSet, ok := stmt.Params[0].(*ast.FnObj)
		if !ok {
			return NewEmptyExecUnknown()
		}

		if len(asEnumSet.Params) != 0 {
			return NewEmptyExecTrue()
		}
	}

	_ = state

	return NewEmptyExecUnknown()
}

func (ver *Verifier) IsInNonEmptyByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if !stmt.NameIs(glob.KeywordIn) {
		return NewEmptyExecUnknown()
	}

	if stmt.TypeEnum != ast.TruePure {
		return NewEmptyExecUnknown()
	}

	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	if stmt.Params[1].String() != glob.KeywordNonEmptySet {
		return NewEmptyExecUnknown()
	}

	if ast.IsEnumSetObj(stmt.Params[0]) {
		asEnumSet, ok := stmt.Params[0].(*ast.FnObj)
		if !ok {
			return NewEmptyExecUnknown()
		}

		if len(asEnumSet.Params) != 0 {
			return NewEmptyExecTrue()
		}
	}

	_ = state

	return NewEmptyExecUnknown()
}
