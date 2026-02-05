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

func (ver *Verifier) verSpecFactByBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	// if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordIsNonEmptyWithItem) {
	// 	return ver.verIsNonEmptyWithItemByBuiltinRules(stmt, state)
	// }

	// if ast.IsTrueSpecFactWithPropName(stmt, glob.KeywordNotEqualSet) {
	// 	return ver.verNotEqualSetByBuiltinRules(stmt, state)
	// }

	if stmt.GetPropName() == glob.KeywordIn {
		if stmt.GetFactType() == ast.FalsePure {
			return ver.falseInFactBuiltinRules(stmt, state)
		} else if stmt.GetFactType() == ast.TruePure {
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

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verNumberTrueLogicRelaOpt_BuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	_ = state

	if _, ok := stmt.(*ast.PureSpecificFactStmt); !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if !stmt.(*ast.PureSpecificFactStmt).IsTrue {
		return ast.NewEmptyUnknownVerRet()
	}

	verRet := ver.btNumberInfixCompareProp(stmt)
	if verRet.IsTrue() || verRet.IsErr() {
		return verRet
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) btNumberInfixCompareProp(stmt ast.SpecificFactStmt) ast.VerRet {
	if !glob.IsBuiltinNumberInfixRelaProp(string(stmt.GetPropName())) {
		return ast.NewEmptyUnknownVerRet()
	}

	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 2 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(asPureStmt.Params)))
	}

	leftNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(asPureStmt.Params[0])
	if err != nil {
		return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
	}
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	rightNumLitExpr, ok, err := ast.MakeObjIntoNumLitExpr(asPureStmt.Params[1])
	if err != nil {
		return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
	}
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	ok, err = glob.NumLitExprCompareOpt(leftNumLitExpr, rightNumLitExpr, string(asPureStmt.PropName))

	if err != nil {
		return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
	}
	if ok {
		return ast.NewTrueVerRet(stmt, nil, "builtin rules")
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verInFactByLeftParamIsNumberExpr(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	_ = state

	if stmt.GetPropName() != glob.KeywordIn {
		return ast.NewEmptyUnknownVerRet()
	}

	// Note: Messages should be handled by the caller, not in defer functions
	isSuccess := false
	defer func() {
		_ = isSuccess
	}()

	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 2 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("builtin logic opt rule should have 2 params, but got %d", len(asPureStmt.Params)))
	}

	// 先评估表达式
	_, toEval := ver.GetValueOfSymbol(asPureStmt.Params[0])

	// 对于 N 和 N_pos，检查是否有运算符、小数点或负号
	if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNatural) || ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNPos) {
		// 检查是否是纯数字（Atom），如果不是（有运算符），则不在 N/N_pos 中
		_, isAtom := toEval.(ast.Atom)
		if !isAtom {
			// 有运算符，不是纯数字，不在 N/N_pos 中
			return ast.NewEmptyUnknownVerRet()
		}

		// 检查是否有小数点
		if ast.IsObjLiterallyRationalNumber(toEval) {
			// 有小数点，不在 N/N_pos 中
			return ast.NewEmptyUnknownVerRet()
		}

		// 检查是否有负号（一元负号运算符）
		if fnObj, ok := asPureStmt.Params[0].(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return ast.NewEmptyUnknownVerRet()
				}
			}
		}
		// 也检查 toEval 是否有负号（如果评估后仍然是负号）
		if fnObj, ok := toEval.(*ast.FnObj); ok {
			if ast.IsObjBuiltinUnaryFn(*fnObj) {
				if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
					// 有负号，不在 N/N_pos 中
					return ast.NewEmptyUnknownVerRet()
				}
			}
		}
	}

	leftObj, ok, err := ast.MakeObjIntoNumLitExpr(toEval)
	if err != nil {
		return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
	}
	if ok {
		if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordReal) {
			isSuccess = glob.IsRealNumLitExpr(leftObj)
			if isSuccess {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s is literally a real number", asPureStmt.Params[0]))
			} else {
				return ast.NewEmptyUnknownVerRet()
			}
		}

		if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNatural) {
			isSuccess = glob.IsNatNumLitExpr(leftObj)
			if isSuccess {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s is literally a natural number", asPureStmt.Params[0]))
			} else {
				return ast.NewEmptyUnknownVerRet()
			}
		}

		if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordInteger) {
			isSuccess = glob.IsIntegerNumLitExpr(leftObj)
			if isSuccess {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s is literally an integer number", asPureStmt.Params[0]))
			} else {
				return ast.NewEmptyUnknownVerRet()
			}
		}

		if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordRational) {
			isSuccess = glob.IsRationalNumLitExpr(leftObj)
			if isSuccess {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s is literally a rational number", asPureStmt.Params[0]))
			} else {
				return ast.NewEmptyUnknownVerRet()
			}
		}

		if ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNPos) {
			isSuccess = glob.IsNPosNumLitExpr(leftObj)
			if isSuccess {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s is literally a positive natural number", asPureStmt.Params[0]))
			} else {
				return ast.NewEmptyUnknownVerRet()
			}
		}
	}

	return ast.NewEmptyUnknownVerRet()
}

// TODO: 理论上任何obj都是set了现在，因为现在set不再是obj了
func (ver *Verifier) verIsASetByBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 1 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsASet, len(asPureStmt.Params)))
	}

	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(asPureStmt.Params[0].String()) {
		return ast.NewEmptyUnknownVerRet()
	}

	return ver.maybeAddSuccessMsgString(state, stmt.String(), fmt.Sprintf("In ZFC set theory, everything is a set. Since Litex is based on ZFC set theory, $%s(x) is true for any object x.", glob.KeywordIsASet), ast.NewTrueVerRet(stmt, nil, ""))
}

func (ver *Verifier) verIsAFiniteSetByBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 1 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsAFiniteSet, len(asPureStmt.Params)))
	}

	if ast.IsListSetObj(asPureStmt.Params[0]) {
		return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set is a finite set.", ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 如果是 cart，那cart的每一位是有限集，所以cart也是有限集
	if ret := ver.verIsAFiniteSetByAllItemsInCartAreNonempty(asPureStmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verIsANonEmptySetByBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 1 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("%s expects 1 parameter, got %d", glob.KeywordIsANonEmptySet, len(asPureStmt.Params)))
	}

	if _, ok := asPureStmt.Params[0].(ast.FnSetObj); ok {
		return ver.verFnSetIsNonEmpty(stmt, state)
	}

	if ast.IsListSetObj(asPureStmt.Params[0]) {
		if len(asPureStmt.Params[0].(*ast.FnObj).Params) > 0 {
			return ver.maybeAddSuccessMsgString(state, stmt.String(), "A list set with at least one element is a nonempty set.", ast.NewTrueVerRet(stmt, nil, ""))
		}
	}

	if _, ok := asPureStmt.Params[0].(ast.Atom); ok {
		paramAsStr := asPureStmt.Params[0].String()
		if glob.IsNPosOrNOrZOrQOrROrRPosOrRNegOrZNegOrQNegOrQPosOrZNot0OrQNot0OrRNot0(paramAsStr) {
			if state.WithMsg {
				return NewVerTrueByBuiltinRule(stmt, []string{fmt.Sprintf("%s is a built-in nonempty set.", paramAsStr)})
			}
			return ast.NewTrueVerRet(stmt, nil, "")
		}
	}

	// 如果是 cart，那cart的每一位是非空集合，所以cart也是非空集合
	if ret := ver.verIsANonEmptySetByAllItemsInCartAreNonempty(asPureStmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	// 如果是形如 fn(X, Y ...) RetSet 这样的函数，那就如果X, Y ... 都是非空集合，RetSet也是非空集合，那就OK了
	// if ret := ver.verIsANonEmptySetByIsFnSetAndAllParamSetsAndRetSetAreNonempty(asPureStmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
	// 	return ret
	// }

	if ret := ver.verIsANonEmptySetByIsPowerSetAndAllParamSetsAndRetSetAreNonempty(asPureStmt.Params[0], state); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verIsAFiniteSetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) ast.VerRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 然后一位一位地检查每一项是否是有限集
	for i := range cartFn.Params {
		isFiniteFact := ast.NewIsAFiniteSetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isFiniteFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	// 如果所有项都是有限集，那么 cart 也是有限集
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a finite set because all its items are finite sets.", cart), ast.NewTrueVerRet(nil, nil, ""))
}

func (ver *Verifier) verIsANonEmptySetByAllItemsInCartAreNonempty(cart ast.Obj, state *VerState) ast.VerRet {
	// 先判断是不是 cart
	cartFn, ok := cart.(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if !ast.IsFn_WithHeadName(cart, glob.KeywordCart) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 然后一位一位地检查每一项是否是非空集合
	for i := range cartFn.Params {
		isNonEmptyFact := ast.NewIsANonEmptySetFact(cartFn.Params[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isNonEmptyFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	// 如果所有项都是非空集合，那么 cart 也是非空集合
	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("cart %s is a nonempty set because all its items are nonempty sets.", cart), ast.NewTrueVerRet(nil, nil, ""))
}

func (ver *Verifier) verIsTupleByBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	_ = state

	if len(asPureStmt.Params) != 1 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("is_tuple expects 1 parameter, got %d", len(asPureStmt.Params)))
	}

	fnObj, ok := asPureStmt.Params[0].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if ast.IsTupleFnObj(fnObj) {
		return ast.NewTrueVerRet(stmt, nil, "")
	}

	equalTo := ver.Env.GetObjTuple(asPureStmt.Params[0])
	if equalTo == nil {
		return ast.NewEmptyUnknownVerRet()
	}

	return ast.NewTrueVerRet(stmt, nil, "")

}

// func (ver *Verifier) verIsANonEmptySetByIsFnSetAndAllParamSetsAndRetSetAreNonempty(fnSet ast.Obj, state *VerState) ast.VerRet {
// 	fnObj, ok := fnSet.(*ast.FnObj)
// 	if !ok {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if _, ok := fnSet.(ast.FnSetObj); !ok {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	_, retSet, err := ast.GetParamSetsAndRetSetFromFnSet(fnObj)
// 	if err != nil {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	isNonEmptyFact := ast.NewIsANonEmptySetFact(retSet, glob.BuiltinLine0)
// 	verRet := ver.VerFactStmt(isNonEmptyFact, state)
// 	if verRet.IsErr() || verRet.IsUnknown() {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("fn set %s is a nonempty set because its return set is a nonempty set.", fnSet), ast.NewTrueVerRet(nil, nil, ""))
// }

// func (ver *Verifier) verIsNonEmptyWithItemByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) ast.VerRet {
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

func (ver *Verifier) verIsANonEmptySetByIsPowerSetAndAllParamSetsAndRetSetAreNonempty(powerSet ast.Obj, state *VerState) ast.VerRet {
	powerSetObj, ok := powerSet.(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if !ast.IsFn_WithHeadName(powerSetObj, glob.KeywordPowerSet) {
		return ast.NewEmptyUnknownVerRet()
	}

	paramInPowerSet := powerSetObj.Params[0]
	isNonEmptyFact := ast.NewIsANonEmptySetFact(paramInPowerSet, glob.BuiltinLine0)
	verRet := ver.VerFactStmt(isNonEmptyFact, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return ast.NewEmptyUnknownVerRet()
	}

	return ver.maybeAddSuccessMsgString(state, "", fmt.Sprintf("power set %s is a nonempty set because its param is a nonempty set.", powerSet), ast.NewTrueVerRet(nil, nil, ""))

}

func (ver *Verifier) verFnSetIsNonEmpty(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 1 {
		return ast.NewEmptyUnknownVerRet()
	}

	switch fnSetObj := asPureStmt.Params[0].(type) {
	case *ast.FnSetObjWithoutName:
		for _, paramSet := range fnSetObj.ParamSets {
			isNonEmptySet := ast.NewIsANonEmptySetFact(paramSet, glob.BuiltinLine0)
			verRet := ver.VerFactStmt(isNonEmptySet, state)
			if verRet.IsNotTrue() {
				return verRet
			}
		}

		isNonEmptySet := ast.NewIsANonEmptySetFact(fnSetObj.RetSet, glob.BuiltinLine0)
		verRet := ver.VerFactStmt(isNonEmptySet, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	case *ast.FnSetObjWithName:
		panic("TODO: verFnSetIsNonEmpty: FnSetObjWithName is not implemented")
	default:
		panic(fmt.Sprintf("unknown function set object type: %T", asPureStmt.Params[0]))
	}

	return ast.NewTrueVerRet(stmt, nil, "")
}
