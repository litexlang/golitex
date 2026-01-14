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

func (ver *Verifier) verSpecFactByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	// if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsNonEmptyWithItem) {
	// 	return ver.verIsNonEmptyWithItemByBuiltinRules(stmt, state)
	// }

	// if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordNotEqualSet) {
	// 	return ver.verNotEqualSetByBuiltinRules(stmt, state)
	// }

	if stmt.NameIs(glob.KeywordIn) {
		if stmt.FactType == ast.FalsePure {
			return ver.falseInFactBuiltinRules(stmt, state)
		} else if stmt.FactType == ast.TruePure {
			return ver.trueInFactBuiltinRules(stmt, state)
		}
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

	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsTuple) {
		return ver.verIsTupleByBuiltinRules(stmt, state)
	}

	if verRet := ver.verNumberTrueLogicRelaOpt_BuiltinRules(stmt, state); verRet.IsErr() {
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

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verNumberTrueLogicRelaOpt_BuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if !stmt.IsPureFact() {
		return glob.NewEmptyVerRetUnknown()
	}

	if !stmt.IsTrue() {
		return glob.NewEmptyVerRetUnknown()
	}

	verRet := ver.btNumberInfixCompareProp(stmt, state)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) btNumberInfixCompareProp(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.PropName)) {
		return glob.NewEmptyVerRetUnknown()
	}

	if len(stmt.Params) != 2 {
		return glob.NewErrVerRet(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[0])
	if err != nil {
		return glob.NewErrVerRet(err.Error())
	}
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(stmt.Params[1])
	if err != nil {
		return glob.NewErrVerRet(err.Error())
	}
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(stmt.PropName))

	if err != nil {
		return glob.NewErrVerRet(err.Error())
	}
	if ok {
		return newMaybeSuccessMsgVerRet(state, stmt, "builtin rules")
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verInFactByLeftParamIsNumberExpr(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	_ = state

	if stmt.PropName != glob.KeywordIn {
		return glob.NewEmptyVerRetUnknown()
	}

	// Note: Messages should be handled by the caller, not in defer functions
	isSuccess := false
	defer func() {
		_ = isSuccess
	}()

	if len(stmt.Params) != 2 {
		return glob.NewErrVerRet(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(stmt.Params)))
	}

	// 先评估表达式
	toEval := ver.evaluateNonNumberLiteralExpr(stmt.Params[0])

	// 对于 N 和 N_pos，检查是否有运算符、小数点或负号
	if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) || ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
		// 检查是否是纯数字（Atom），如果不是（有运算符），则不在 N/N_pos 中
		_, isAtom := toEval.(ast.Atom)
		if !isAtom {
			// 有运算符，不是纯数字，不在 N/N_pos 中
			return glob.NewEmptyVerRetUnknown()
		}

		// 检查是否有小数点
		if ast.IsObjLiterallyRationalNumber(toEval) {
			// 有小数点，不在 N/N_pos 中
			return glob.NewEmptyVerRetUnknown()
		}

		// 检查是否有负号（一元负号运算符）
		if fnObj, ok := stmt.Params[0].(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return glob.NewEmptyVerRetUnknown()
				}
			}
		}
		// 也检查 toEval 是否有负号（如果评估后仍然是负号）
		if fnObj, ok := toEval.(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return glob.NewEmptyVerRetUnknown()
				}
			}
		}
	}

	leftObj, ok, err := ast.MakeObjIntoNumLitExpr(toEval)
	if err != nil {
		return glob.NewErrVerRet(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftObj)
			if isSuccess {
				return (glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is literally a real number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftObj)
			if isSuccess {
				return (glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is literally a natural number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftObj)
			if isSuccess {
				return (glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is literally an integer number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftObj)
			if isSuccess {
				return (glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is literally a rational number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		if ast.IsAtomObjAndEqualToStr(stmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftObj)
			if isSuccess {
				return (glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("%s is literally a positive natural number", stmt.Params[0])}))
			} else {
				return glob.NewEmptyVerRetUnknown()
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

// verNotEqualSetByBuiltinRules verifies not_equal_set(a, b) by checking:
// - a != b
// func (ver *Verifier) verNotEqualSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
// 	if len(stmt.Params) != 2 {
// 		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{fmt.Sprintf("not_equal_set expects 2 parameters, got %d", len(stmt.Params))})
// 	}

// 	a := stmt.Params[0]
// 	b := stmt.Params[1]

// 	// Create a != b fact
// 	notEqualFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{a, b}, stmt.Line)
// 	verRet := ver.VerFactStmt(notEqualFact, state)
// 	if verRet.IsNotTrue() {
// 		return verRet
// 	}

// 	// a != b is true, so not_equal_set(a, b) is true
// 	msg := fmt.Sprintf("not_equal_set(%s, %s) is true because %s != %s", a, b, a, b)
// 	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.NewEmptyVerRetTrue())
// }

// TODO: 理论上任何obj都是set了现在，因为现在set不再是obj了
func (ver *Verifier) verIsASetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if len(stmt.Params) != 1 {
		return glob.NewErrVerRet(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsASet, len(stmt.Params)))
	}

	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(stmt.Params[0].String()) {
		return glob.NewEmptyVerRetUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), fmt.Sprintf("In ZFC set theory, everything is a set. Since Litex is based on ZFC set theory, $%s(x) is true for any object x.", glob.KeywordIsASet), glob.NewEmptyVerRetTrue())
}

func (ver *Verifier) verIsAFiniteSetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if len(stmt.Params) != 1 {
		return glob.NewErrVerRet(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsAFiniteSet, len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set is a finite set.", glob.NewEmptyVerRetTrue())
	}

	// 如果是 cart，那cart的每一位是有限集，所以cart也是有限集
	if ret := ver.verIsAFiniteSetByAllItemsInCartAreNonempty(stmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verIsANonEmptySetByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if len(stmt.Params) != 1 {
		return glob.NewErrVerRet(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsANonEmptySet, len(stmt.Params)))
	}

	if ast.IsListSetObj(stmt.Params[0]) {
		if len(stmt.Params[0].(*ast.FnObj).Params) > 0 {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set with at least one element is a nonempty set.", glob.NewEmptyVerRetTrue())
		}
	}

	if _, ok := stmt.Params[0].(ast.Atom); ok {
		paramAsStr := stmt.Params[0].String()
		if glob.IsNPosOrNOrZOrQOrR(paramAsStr) {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), fmt.Sprintf("%s & %s & %s & %s & %s are nonempty sets.", glob.KeywordNPos, glob.KeywordNatural, glob.KeywordInteger, glob.KeywordRational, glob.KeywordReal), glob.NewEmptyVerRetTrue())
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

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verIsAFiniteSetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) *glob.VerRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return glob.NewEmptyVerRetUnknown()
	}

	// 然后一位一位地检查每一项是否是有限集
	for i := range cartFn.Params {
		isFiniteFact := ast.NewIsAFiniteSetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isFiniteFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	// 如果所有项都是有限集，那么 cart 也是有限集
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a finite set because all its items are finite sets.", cart), glob.NewEmptyVerRetTrue())
}

func (ver *Verifier) verIsANonEmptySetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) *glob.VerRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return glob.NewEmptyVerRetUnknown()
	}

	// 然后一位一位地检查每一项是否是非空集合
	for i := range cartFn.Params {
		isNonEmptyFact := ast.NewIsANonEmptySetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isNonEmptyFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	// 如果所有项都是非空集合，那么 cart 也是非空集合
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a nonempty set because all its items are nonempty sets.", cart), glob.NewEmptyVerRetTrue())
}

func (ver *Verifier) verIsTupleByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	_ = state

	if len(stmt.Params) != 1 {
		return glob.NewErrVerRet(fmt.Sprintf("is_tuple expects 1 parameter, got %d", len(stmt.Params)))
	}

	fnObj, ok := stmt.Params[0].(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if ast.IsTupleFnObj(fnObj) {
		return glob.NewEmptyVerRetTrue()
	}

	equalTo := ver.Env.GetObjTuple(stmt.Params[0])
	if equalTo == nil {
		return glob.NewEmptyVerRetUnknown()
	}

	return glob.NewEmptyVerRetTrue()

}

func (ver *Verifier) verIsANonEmptySetByIsFnSetAndAllParamSetsAndRetSetAreNonempty(fnSet ast.Obj, state *VerState) *glob.VerRet {
	fnObj, ok := fnSet.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if !ast.IsFnSet(fnObj) {
		return glob.NewEmptyVerRetUnknown()
	}

	_, retSet, err := ast.GetParamSetsAndRetSetFromFnSet(fnObj)
	if err != nil {
		return glob.NewEmptyVerRetUnknown()
	}

	isNonEmptyFact := ast.NewIsANonEmptySetFact(retSet, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isNonEmptyFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return glob.NewEmptyVerRetUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("fn set %s is a nonempty set because its return set is a nonempty set.", fnSet), glob.NewEmptyVerRetTrue())
}

// func (ver *Verifier) verIsNonEmptyWithItemByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
// 	if len(stmt.Params) != 2 {
// 		return glob.NewVerMsg2(glob.StmtRetTypeError, stmt.String(), stmt.GetLine(), []string{fmt.Sprintf("is_nonempty_with_item expects 1 parameter, got %d", len(stmt.Params))})
// 	}

// 	inFact := ast.NewInFactWithObj(stmt.Params[1], stmt.Params[0])
// 	verRet := ver.VerFactStmt(inFact, state)
// 	if verRet.IsNotTrue() {
// 		return verRet
// 	}

// 	return ver.maybeAddSuccessMsgString(state, stmt.String(), "is_nonempty_with_item is true because the item is in the set.", glob.NewEmptyVerRetTrue())

// }

func (ver *Verifier) verIsANonEmptySetByIsPowerSetAndAllParamSetsAndRetSetAreNonempty(powerSet ast.Obj, state *VerState) *glob.VerRet {
	powerSetObj, ok := powerSet.(*ast.FnObj)
	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

	if !ast.IsFn_WithHeadName(powerSetObj, glob.KeywordPowerSet) {
		return glob.NewEmptyVerRetUnknown()
	}

	paramInPowerSet := powerSetObj.Params[0]
	isNonEmptyFact := ast.NewIsANonEmptySetFact(paramInPowerSet, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isNonEmptyFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return glob.NewEmptyVerRetUnknown()
	}

	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("power set %s is a nonempty set because its param is a nonempty set.", powerSet), glob.NewEmptyVerRetTrue())

}
