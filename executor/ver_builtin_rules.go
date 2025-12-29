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
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFactByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsNonEmptyWithItem) {
		return ver.verIsNonEmptyWithItemByBuiltinRules(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordEqualSet) {
		return ver.verEqualSetByBuiltinRules(stmt, state)
	}

	if stmt.NameIs(glob.KeywordIn) {
		if stmt.FactType == ast.FalsePure {
			return ver.falseInFactBuiltinRules(stmt, state)
		}
		return ver.trueInFactBuiltinRules(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsASet) {
		return ver.verIsASetByBuiltinRules(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsAFiniteSet) {
		return ver.verIsAFiniteSetByBuiltinRules(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsANonEmptySet) {
		return ver.verIsANonEmptySetByBuiltinRules(stmt, state)
	}

	// if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordItemExistsIn) {
	// 	return ver.verItemExistsInByBuiltinRules(stmt, state)
	// }

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordEqualTuple) {
		return ver.verEqualTupleByBuiltinRules(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsTuple) {
		return ver.verIsTupleByBuiltinRules(stmt, state)
	}

	if verRet := ver.verNumberLogicRelaOpt_BuiltinRules(stmt, state); verRet.IsErr() {
		return verRet
	} else if verRet.IsTrue() {
		return verRet
	}

	if ast.IsFalseSpecFactWithPropName(stmt, glob.KeySymbolEqual) {
		return ver.verNotTrueEqualFact_BuiltinRules_WithState(stmt, state)
	}

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsCart) {
		return ver.verIsCartByBuiltinRules(stmt, state)
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verNumberLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if !stmt.IsTrue() {
		return glob.NewEmptyStmtUnknown()
	}

	verRet := ver.btNumberInfixCompareProp(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return glob.NewEmptyStmtUnknown()
	}

	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if ok {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "builtin rules", glob.NewEmptyStmtTrue())
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verInFactByLeftParamIsNumberExpr(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	_ = state

	if stmt.PropName != glob.KeywordIn {
		return glob.NewEmptyStmtUnknown()
	}

	// Note: Messages should be handled by the caller, not in defer functions
	isSuccess := false
	defer func() {
		_ = isSuccess
	}()

	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	// 先评估表达式
	toEval := ver.evaluateNonNumberLiteralExpr(stmt.Params[0])

	// 对于 N 和 N_pos，检查是否有运算符、小数点或负号
	if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) || ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
		// 检查是否是纯数字（Atom），如果不是（有运算符），则不在 N/N_pos 中
		_, isAtom := toEval.(ast.Atom)
		if !isAtom {
			// 有运算符，不是纯数字，不在 N/N_pos 中
			return glob.NewEmptyStmtUnknown()
		}

		// 检查是否有小数点
		if ast.IsObjLiterallyRationalNumber(toEval) {
			// 有小数点，不在 N/N_pos 中
			return glob.NewEmptyStmtUnknown()
		}

		// 检查是否有负号（一元负号运算符）
		if fnObj, ok := stmt.Params[0].(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return glob.NewEmptyStmtUnknown()
				}
			}
		}
		// 也检查 toEval 是否有负号（如果评估后仍然是负号）
		if fnObj, ok := toEval.(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return glob.NewEmptyStmtUnknown()
				}
			}
		}
	}

	leftObj, ok, err := ast.MakeObjIntoNumLitExpr(toEval)
	if err != nil {
		return glob.ErrRet(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftObj)
			if isSuccess {
				return glob.NewStmtTrueWithVerifyProcess(glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{fmt.Sprintf("%s is literally a real number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyStmtUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftObj)
			if isSuccess {
				return glob.NewStmtTrueWithVerifyProcess(glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{fmt.Sprintf("%s is literally a natural number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyStmtUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftObj)
			if isSuccess {
				return glob.NewStmtTrueWithVerifyProcess(glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{fmt.Sprintf("%s is literally an integer number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyStmtUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftObj)
			if isSuccess {
				return glob.NewStmtTrueWithVerifyProcess(glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{fmt.Sprintf("%s is literally a rational number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyStmtUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftObj)
			if isSuccess {
				return glob.NewStmtTrueWithVerifyProcess(glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), stmt.Line, []string{fmt.Sprintf("%s is literally a positive natural number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyStmtUnknown()
			}
		}
	}

	return glob.NewEmptyStmtUnknown()
}

// verEqualSetByBuiltinRules verifies equal_set(a, b) by checking:
// - forall t a : t $in b
// - forall t b : t $in a
func (ver *Verifier) verEqualSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("equal_set expects 2 parameters, got %d", len(stmt.Params)))
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
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyStmtTrue())
}

// TODO: 理论上任何obj都是set了现在，因为现在set不再是obj了
func (ver *Verifier) verIsASetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 1 {
		return glob.ErrRet(fmt.Sprintf("is_a_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.Params[0].String()) {
		return glob.NewEmptyStmtUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), "In ZFC set theory, everything is a set. Since Litex is based on ZFC set theory, $is_a_set(x) is true for any object x.", glob.NewEmptyStmtTrue())
}

func (ver *Verifier) verIsAFiniteSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 1 {
		return glob.ErrRet(fmt.Sprintf("is_a_finite_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set is a finite set.", glob.NewEmptyStmtTrue())
	}

	// 如果是 cart，那cart的每一位是有限集，所以cart也是有限集
	if ret := ver.verIsAFiniteSetByAllItemsInCartAreNonempty(stmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verIsANonEmptySetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 1 {
		return glob.ErrRet(fmt.Sprintf("is_a_nonempty_set expects 1 parameter, got %d", len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		if len(stmt.Params[0].(*ast.FnObj).Params) > 0 {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set with at least one element is a nonempty set.", glob.NewEmptyStmtTrue())
		}
	}

	if _, ok := stmt.Params[0].(ast.Atom); ok {
		paramAsStr := stmt.Params[0].String()
		if glob.IsNPosOrNOrZOrQOrR(paramAsStr) {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), fmt.Sprintf("%s & %s & %s & %s & %s are nonempty sets.", glob.KeywordNPos, glob.KeywordNatural, glob.KeywordInteger, glob.KeywordRational, glob.KeywordReal), glob.NewEmptyStmtTrue())
		}
	}

	// 如果是 cart，那cart的每一位是非空集合，所以cart也是非空集合
	if ret := ver.verIsANonEmptySetByAllItemsInCartAreNonempty(stmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	// 如果是形如 fn(X, Y ...) RetSet 这样的函数，那就如果X, Y ... 都是非空集合，RetSet也是非空集合，那就OK了
	if ret := ver.verIsANonEmptySetByIsFnSetAndAllParamSetsAndRetSetAreNonempty(stmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ver.verIsANonEmptySetByIsPowerSetAndAllParamSetsAndRetSetAreNonempty(stmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.NewEmptyStmtUnknown()
}

func (ver *Verifier) verIsAFiniteSetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) *glob.StmtRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return glob.NewEmptyStmtUnknown()
	}

	// 然后一位一位地检查每一项是否是有限集
	for i := range cartFn.Params {
		isFiniteFact := ast.NewIsAFiniteSetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isFiniteFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return glob.NewEmptyStmtUnknown()
		}
	}

	// 如果所有项都是有限集，那么 cart 也是有限集
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a finite set because all its items are finite sets.", cart), glob.NewEmptyStmtTrue())
}

func (ver *Verifier) verIsANonEmptySetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) *glob.StmtRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return glob.NewEmptyStmtUnknown()
	}

	// 然后一位一位地检查每一项是否是非空集合
	for i := range cartFn.Params {
		isNonEmptyFact := ast.NewIsANonEmptySetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isNonEmptyFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return glob.NewEmptyStmtUnknown()
		}
	}

	// 如果所有项都是非空集合，那么 cart 也是非空集合
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a nonempty set because all its items are nonempty sets.", cart), glob.NewEmptyStmtTrue())
}

func (ver *Verifier) verIsTupleByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	_ = state

	if len(stmt.Params) != 1 {
		return glob.ErrRet(fmt.Sprintf("is_tuple expects 1 parameter, got %d", len(stmt.Params)))
	}

	fnObj, ok := stmt.Params[0].(*ast.FnObj)
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	if ast.IsTupleFnObj(fnObj) {
		return glob.NewEmptyStmtTrue()
	}

	equalTo := ver.Env.GetObjTuple(stmt.Params[0])
	if equalTo == nil {
		return glob.NewEmptyStmtUnknown()
	}

	return glob.NewEmptyStmtTrue()

}

func (ver *Verifier) verIsANonEmptySetByIsFnSetAndAllParamSetsAndRetSetAreNonempty(fnSet ast.Obj, state *VerState) *glob.StmtRet {
	fnObj, ok := fnSet.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	if !ast.IsFnSet(fnObj) {
		return glob.NewEmptyStmtUnknown()
	}

	paramSets, retSet, err := ast.GetParamSetsAndRetSetFromFnSet(fnObj)
	if err != nil {
		return glob.NewEmptyStmtUnknown()
	}

	for _, paramSet := range paramSets {
		isNonEmptyFact := ast.NewIsANonEmptySetFact(paramSet, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isNonEmptyFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return glob.NewEmptyStmtUnknown()
		}
	}

	isNonEmptyFact := ast.NewIsANonEmptySetFact(retSet, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isNonEmptyFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return glob.NewEmptyStmtUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("fn set %s is a nonempty set because all its param sets and ret set are nonempty sets.", fnSet), glob.NewEmptyStmtTrue())
}

func (ver *Verifier) verIsNonEmptyWithItemByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("is_nonempty_with_item expects 1 parameter, got %d", len(stmt.Params)))
	}

	inFact := ast.NewInFactWithObj(stmt.Params[1], stmt.Params[0])
	verRet := ver.VerFactStmt(inFact, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), "is_nonempty_with_item is true because the item is in the set.", glob.NewEmptyStmtTrue())

}

func (ver *Verifier) verIsANonEmptySetByIsPowerSetAndAllParamSetsAndRetSetAreNonempty(powerSet ast.Obj, state *VerState) *glob.StmtRet {
	powerSetObj, ok := powerSet.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyStmtUnknown()
	}

	if !ast.IsFn_WithHeadName(powerSetObj, glob.KeywordPowerSet) {
		return glob.NewEmptyStmtUnknown()
	}

	paramInPowerSet := powerSetObj.Params[0]
	isNonEmptyFact := ast.NewIsANonEmptySetFact(paramInPowerSet, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isNonEmptyFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return glob.NewEmptyStmtUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("power set %s is a nonempty set because its param is a nonempty set.", powerSet), glob.NewEmptyStmtTrue())

}
