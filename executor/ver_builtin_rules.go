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
	}

	// if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TrueExist_St {
	// 	return ver.trueExistInSt(stmt, state)
	// }

	if stmt.NameIs(glob.KeywordIsASet) && stmt.TypeEnum == ast.TruePure {
		return ver.verIsASetByBuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIsAFiniteSet) && stmt.TypeEnum == ast.TruePure {
		return ver.verIsAFiniteSetByBuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIsANonEmptySet) && stmt.TypeEnum == ast.TruePure {
		return ver.verIsANonEmptySetByBuiltinRules(stmt, state)
	}

	// if stmt.NameIs(glob.KeywordItemExistsIn) && stmt.TypeEnum == ast.TruePure {
	// 	return ver.verItemExistsInByBuiltinRules(stmt, state)
	// }

	if stmt.NameIs(glob.KeywordEqualSet) && stmt.TypeEnum == ast.TruePure {
		return ver.verEqualSetByBuiltinRules(stmt, state)
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

func (ver *Verifier) verInFactByLeftParamIsNumberExpr(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
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

	leftObj, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return NewExecErr(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftObj)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftObj)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftObj)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftObj)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftObj)
			if isSuccess {
				return NewEmptyExecTrue()
			} else {
				return NewEmptyExecUnknown()
			}
		}
	}

	return NewEmptyExecUnknown()
}

// func (ver *Verifier) verItemExistsInByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
// 	if len(stmt.Params) != 1 {
// 		return NewExecErr(fmt.Sprintf("builtin logic opt rule should have 1 param, but got %d", len(stmt.Params)))
// 	}

// 	if ast.IsListSetObj(stmt.Params[0]) {
// 		asEnumSet, ok := stmt.Params[0].(*ast.FnObj)
// 		if !ok {
// 			return NewEmptyExecUnknown()
// 		}

// 		if len(asEnumSet.Params) != 0 {
// 			return NewEmptyExecTrue()
// 		}
// 	}

// 	_ = state

// 	return NewEmptyExecUnknown()
// }

// verEqualSetByBuiltinRules verifies equal_set(a, b) by checking:
// - forall t a : t $in b
// - forall t b : t $in a
func (ver *Verifier) verEqualSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 2 {
		return NewExecErr(fmt.Sprintf("equal_set expects 2 parameters, got %d", len(stmt.Params)))
	}

	a := stmt.Params[0]
	b := stmt.Params[1]

	// Create forall t1 a : t1 $in b
	forall1 := ast.NewUniFact(
		[]string{"t"},
		[]ast.Obj{a},
		[]ast.FactStmt{},
		[]ast.FactStmt{
			ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), b}, stmt.Line),
		},
		stmt.Line,
	)

	// Create forall t2 b : t2 $in a
	forall2 := ast.NewUniFact(
		[]string{"t"},
		[]ast.Obj{b},
		[]ast.FactStmt{},
		[]ast.FactStmt{
			ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom("t"), a}, stmt.Line),
		},
		stmt.Line,
	)

	// Verify both forall statements
	verRet1 := ver.VerFactStmt(forall1, state)
	if verRet1.IsNotTrue() {
		return verRet1
	}

	verRet2 := ver.VerFactStmt(forall2, state)
	if verRet2.IsNotTrue() {
		return verRet2
	}

	// Both forall statements are true, so equal_set(a, b) is true
	msg := fmt.Sprintf("equal_set(%s, %s) is true because forall t %s : t $in %s and forall t %s : t $in %s", a, b, a, b, b, a)
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewEmptyExecTrue())
}

// TODO: 理论上任何obj都是set了现在，因为现在set不再是obj了
func (ver *Verifier) verIsASetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 1 {
		return NewExecErr(fmt.Sprintf("is_a_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.Params[0].String()) {
		return NewEmptyExecUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), "In ZFC set theory, everything except set itself is a set. In Litex, any object except set, nonempty_set, finite_set is a set.", NewEmptyExecTrue())
}

func (ver *Verifier) verIsAFiniteSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 1 {
		return NewExecErr(fmt.Sprintf("is_a_finite_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set is a finite set.", NewEmptyExecTrue())
	}

	return NewEmptyExecUnknown()
}

func (ver *Verifier) verIsANonEmptySetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	if len(stmt.Params) != 1 {
		return NewExecErr(fmt.Sprintf("is_a_nonempty_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		if len(stmt.Params[0].(*ast.FnObj).Params) > 0 {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set with at least one element is a nonempty set.", NewEmptyExecTrue())
		}
	}

	if _, ok := stmt.Params[0].(ast.Atom); ok {
		paramAsStr := stmt.Params[0].String()
		if glob.IsNPosOrNOrZOrQOrR(paramAsStr) {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "A number is a nonempty set.", NewEmptyExecTrue())
		}
	}

	return NewEmptyExecUnknown()
}
