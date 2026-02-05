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
	"strconv"
)

func (ver *Verifier) trueInFactBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	if len(stmt.(*ast.PureSpecificFactStmt).Params) != 2 {
		return ast.NewErrVerRet(stmt).AddExtraInfo(fmt.Sprintf("invalid number of parameters for in fact: %d", len(stmt.(*ast.PureSpecificFactStmt).Params)))
	}

	verRet := ver.verInFactByLeftParamIsNumberExpr(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfArithmeticFn(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfSuperFn(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightParamIsN_Z_Q_R_N_pos_Z_pos_R_pos_etc_BySpecMem_ReturnValueOfUserDefinedFnInFnReturn(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightParamIsFnTemplateFact(stmt, state)
	if verRet.IsErr() {
		return ast.NewErrVerRet(stmt).AddExtraInfo(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightParamIsSetProduct(stmt, state)
	if verRet.IsErr() {
		return ast.NewErrVerRet(stmt).AddExtraInfo(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightParamIsCartSet(stmt, state)
	if verRet.IsErr() {
		return ast.NewErrVerRet(stmt).AddExtraInfo(verRet.String())
	}
	if verRet.IsTrue() {
		return verRet
	}

	// ast.VerRet = ver.verInFactByLeftIsFnTemplateAndRightIsKeywordSet(stmt, state)
	// if verRet.IsErr() || verRet.IsTrue() {
	// 	return verRet
	// }

	// cart(R, R) $in nonempty_set
	verRet = ver.verInFactByLeftIsCartSetAndRightIsKeywordNonemptySet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// x[1] $in some_set
	verRet = ver.verInFactByLeftIsIndexOfObjInSomeSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// x $in {x R: x > 0}
	verRet = ver.verInFactByRightIsSetBuilder(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightIsListSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verInFactByRightIsPowerSet(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// x $in power_set(X)
	// ast.VerRet = ver.verInFactByRightIsPowerSet(stmt, state)
	// if verRet.IsErr() {
	// 	return verRet
	// }
	// if verRet.IsTrue() {
	// 	return verRet
	// }

	verRet = ver.verFnSetIsNonEmpty(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verInFactByLeftIsCartSetAndRightIsKeywordNonemptySet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	if !ast.IsFn_WithHeadName(stmt.(*ast.PureSpecificFactStmt).Params[0], glob.KeywordCart) {
		return ast.NewEmptyUnknownVerRet()
	}

	asFnObj, ok := stmt.(*ast.PureSpecificFactStmt).Params[0].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 所有的cart里的参数都是非空集合
	for i := range asFnObj.Params {
		verRet := ver.VerFactStmt(ast.NewIsANonEmptySetFact(asFnObj.Params[i], stmt.GetLine()), state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("all arguments of %s are in nonempty.", stmt.(*ast.PureSpecificFactStmt).Params[0]))
}

func (ver *Verifier) verInFactByLeftParamIsReturnValueOfArithmeticFn(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {

	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	ok = ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordReal)
	if ok {
		ok = ast.IsFn_WithHeadNameInSlice(asPureStmt.Params[0], map[string]struct{}{glob.KeySymbolPlus: {}, glob.KeySymbolMinus: {}, glob.KeySymbolStar: {}, glob.KeySymbolSlash: {}, glob.KeySymbolPower: {}, glob.KeywordVal: {}})

		if ok {
			msg := fmt.Sprintf("return value of builtin arithmetic function %s is in Real", asPureStmt.Params[0])
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
		}
		return ast.NewEmptyUnknownVerRet()
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verInFactByRightParamIsFnTemplateFact(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if asFcFn, ok := asPureStmt.Params[1].(*ast.FnObj); ok {
		if ast.IsAnonymousFnSet(asFcFn) {
			verRet := ver.ver_In_FnFcFn_FnTT(asPureStmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", asPureStmt.Params[1], asPureStmt.Params[0], asPureStmt.Params[1])
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		} else {
			// return false, nil
			verRet := ver.ver_In_FnTT(asPureStmt.Params[0], asFcFn, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("dom of template %s is in the domain of the template where function %s is in. Also, the return value of the function is in the return set of the template where function %s is in", asPureStmt.Params[1], asPureStmt.Params[0], asPureStmt.Params[1])
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		}
		return ast.NewEmptyUnknownVerRet()
		// }
	}

	return ast.NewEmptyUnknownVerRet()
}

// func (ver *Verifier) verInSet_btRules(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
// 	var ast.VerRet *glob.GlobRet
// 	ok := ast.IsObjAtomEqualToGivenString(stmt.Params[1], glob.KeywordSet)
// 	if !ok {
// 		return NewExecEmptyUnknown()
// 	}

// 	// 如果它是N, Z, Q, R, C, 则直接返回true
// 	ok = ast.IsObjAtomEqualToGivenString(stmt.Params[0], glob.KeywordNatural) ||
// 		ast.IsObjAtomEqualToGivenString(stmt.Params[0], glob.KeywordInteger) ||
// 		ast.IsObjAtomEqualToGivenString(stmt.Params[0], glob.KeywordRational) ||
// 		ast.IsObjAtomEqualToGivenString(stmt.Params[0], glob.KeywordReal) ||
// 		ast.IsObjAtomEqualToGivenString(stmt.Params[0], glob.KeywordNPos)
// 	if ok {
// 		return ver.processOkMsg(state, stmt.String(), "%s is a builtin set", stmt.Params[0])
// 	}

// 	// 如果它是 cart(...)，直接返回true
// 	if ast.IsFn_WithHeadName(stmt.Params[0], glob.KeywordCart) {
// 		return ver.processOkMsg(state, stmt.String(), "%s is a builtin set", stmt.Params[0])
// 	}

// 	verRet = ver.FnTemplateIsASet(stmt, state.GetNoMsg())
// 	if verRet.IsErr() {
// 		return verRet
// 	}
// 	if verRet.IsTrue() {
// 		msg := "When parameter sets of a fn template are all sets, then the fn template is a set"
// 		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, glob.GlobTrue(msg))
// 	}

// 	// 如果是被定义好了的fn_template，则直接返回true
// 	asFcFn, ok := stmt.Params[1].(*ast.FnObj)
// 	if !ok {
// 		return NewExecEmptyUnknown()
// 	}
// 	ok = ast.IsFnTemplate_ObjFn(asFcFn)
// 	if ok {
// 		return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", stmt.Params[0])
// 	}

// 	if leftAsAtom, ok := stmt.Params[0].(ast.Atom); ok {
// 		// _, ok := ver.env.GetFnTemplateDef(leftAsAtom)
// 		fnDef := ver.Env.GetLatestFnT_GivenNameIsIn(leftAsAtom.String())
// 		if fnDef != nil {
// 			return ver.processOkMsg(state, stmt.String(), "%s is a fn template and all fn templates are sets", leftAsAtom)
// 		}
// 	}

// 	return NewExecEmptyUnknown()
// }

func (ver *Verifier) falseInFactBuiltinRules(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 任何东西不在空集里
	verRet := ver.nothingIsInEmptySet(asPureStmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	verRet = ver.objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 如果你是数字，那么必须要真的长成自然数的形状，才是自然数，否则不行
	// 也就是说，如果数字字面上看起来不像自然数（是小数、负数或表达式），可以证明它不在自然数中
	verRet = ver.litNumNotInNaturalByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 如果在证明 not in Z
	verRet = ver.litNumNotInIntegerByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 如果证明 not in N_pos
	verRet = ver.litNumNotInNPosByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 类似 3.5 这种数不在 Z, N, N_pos 里
	verRet = ver.litNumNotInIntegerByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	// 负数不在N, N_pos里
	verRet = ver.litNumNotInNaturalByLiteralShape(stmt, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return ast.NewEmptyUnknownVerRet()
}

// TODO 需要先证明一下它是finite set 去开始验证 len(n) = 0
func (ver *Verifier) nothingIsInEmptySet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	verRet := ver.VerFactStmt(ast.NewIsAFiniteSetFact(asPureStmt.Params[1], stmt.GetLine()), state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	lenOverStmtName := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{asPureStmt.Params[1]})
	equalFact := ast.EqualFact(lenOverStmtName, ast.Atom("0"))
	verRet = ver.VerFactStmt(equalFact, state)
	return verRet
}

func (ver *Verifier) objNotInSetWhenAllItemsInThatSetAreNotEqualToIt(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if asPureStmt.IsTrue {
		return ast.NewEmptyUnknownVerRet()
	}

	notAllItemsInThatSetAreNotEqualToIt := ast.NewUniFact([]string{"x"}, []ast.Obj{asPureStmt.Params[1]}, []ast.Spec_OrFact{}, []ast.Spec_OrFact{ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom("x"), asPureStmt.Params[0]}, asPureStmt.GetLine())}, asPureStmt.GetLine())

	verRet := ver.VerFactStmt(notAllItemsInThatSetAreNotEqualToIt, state)
	return verRet
}

// verInCartSet_ByTuple verifies a $in cart(...) by checking if the tuple's elements are in corresponding cart sets
// func (ver *Verifier) verInCartSet_ByTuple(stmt *ast.SpecFactStmt, state *VerState) *glob.GlobRet {
// 	// Check if right side is cart(...)
// 	cartSet, ok := stmt.Params[1].(*ast.FnObj)
// 	if !ok {
// 		return NewExecEmptyUnknown()
// 	}
// 	if !ast.IsAtomObjAndEqualToStr(cartSet.FnHead, glob.KeywordCart) {
// 		return NewExecEmptyUnknown()
// 	}

// 	// Get obj from ObjFromCartSetMem
// 	obj := stmt.Params[0]
// 	item := ver.Env.GetObjFromCartSetMemItem(obj)
// 	if item == nil {
// 		return NewExecEmptyUnknown()
// 	}

// 	// Get EqualTo tuple
// 	tuple := item.EqualToOrNil
// 	if tuple == nil {
// 		return NewExecEmptyUnknown()
// 	}

// 	tupleAsFn, ok := tuple.(*ast.FnObj)
// 	if !ok || !ast.IsTupleFnObj(tupleAsFn) {
// 		return NewExecEmptyUnknown()
// 	}

// 	// Check that tuple length matches cart set length
// 	if len(tupleAsFn.Params) != len(cartSet.Params) {
// 		return glob.NewErrVerRet(fmt.Sprintf("tuple length (%d) does not match cart set length (%d) in %s", len(tupleAsFn.Params), len(cartSet.Params), stmt))
// 	}

// 	// Check that each element of tuple is in the corresponding cart set
// 	for i := range len(tupleAsFn.Params) {
// 		inFact := ast.NewInFactWithObj(tupleAsFn.Params[i], cartSet.Params[i])
// 		verRet := ver.VerFactStmt(inFact, state)
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsUnknown() {
// 			return NewExecEmptyUnknown()
// 		}
// 	}

// 	msg := fmt.Sprintf("each element in tuple %s is in corresponding cart set %s", tuple, cartSet)
// 	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, NewExecEmptyTrue())
// }

func (ver *Verifier) verInFactByRightParamIsSetProduct(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// left must be (x, y, ...) right must be product(xSet, ySet, ...)
	fcFn, ok := asPureStmt.Params[0].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}
	// ok = ast.IsAtomObjAndEqualToStr(fcFn.FnHead, glob.TupleFcFnHead)
	// if !ok {
	// 	return NewExecEmptyUnknown()
	// }

	setProductFn, ok := asPureStmt.Params[1].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(fcFn.Params) != len(setProductFn.Params) {
		return ast.NewEmptyUnknownVerRet()
	}

	for i := range len(fcFn.Params) {
		inFact := ast.NewInFactWithParamObj(fcFn.Params[i], setProductFn.Params[i], stmt.GetLine())
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	msg := fmt.Sprintf("each item in tuple %s is in corresponding set %s", asPureStmt.Params[0], asPureStmt.Params[1])
	return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
}

// getCartSetFromObj gets the cart set from obj if obj = cart(...)
// Returns the cart set if found, nil otherwise
func (ver *Verifier) getCartSetFromObj(obj ast.Obj) *ast.FnObj {
	equalObjs, ok := ver.Env.GetEqualObjs(obj)
	if !ok || equalObjs == nil {
		return nil
	}
	// Look for a cart set in the equal facts
	for _, equalObj := range *equalObjs {
		if cartAsFn, ok := equalObj.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
			return cartAsFn
		}
	}
	return nil
}

// verInCartSet_DimAndElements verifies a $in cart(...) by checking:
// 1. dim(a) = dim(cart(...))
// 2. a[i] $in cart(...).Params[i-1] for each i
func (ver *Verifier) verInCartSet_DimAndElements(obj ast.Obj, cartSet *ast.FnObj, objCartSet *ast.FnObj, state *VerState) ast.VerRet {
	// Step 1: Verify dim(a) = dim(cart(...))
	// dim(cart(...)) = len(cartSet.Params)
	cartDimValue := len(cartSet.Params)

	ret := ver.VerFactStmt(ast.NewEqualFact(ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj}), ast.Atom(strconv.Itoa(cartDimValue))), state)
	if ret.IsErr() {
		return ret
	}
	if ret.IsUnknown() {
		return ast.NewEmptyUnknownVerRet()
	}

	// Step 2: Verify a[i] $in cartSet.Params[i-1] for each i
	for i := range len(cartSet.Params) {
		index := i + 1 // index starts from 1
		indexObj := ast.Atom(fmt.Sprintf("%d", index))

		// If obj = cart(...), use proj(obj, i) to get a[i]
		var objElement ast.Obj
		if objCartSet != nil {
			// obj = cart(...), so a[i] = proj(cart(...), i) = cart(...).Params[i-1]
			objElement = objCartSet.Params[i]
		} else {
			// Create indexed object: a[i]
			objElement = ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{obj, indexObj})
		}

		// Verify a[i] $in cartSet.Params[i]
		inFact := ast.NewInFactWithObj(objElement, cartSet.Params[i])
		verRet := ver.VerFactStmt(inFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	msg := fmt.Sprintf("dim(%s) = %d and each element %s[i] is in corresponding cart set %s", obj, cartDimValue, obj, cartSet)
	return ast.NewTrueVerRet(nil, nil, "").AddExtraInfo(msg)
}

// verInFactByRightParamIsCartSet verifies a $in cart(...) by checking:
// 1. dim(a) = dim(cart(...))
// 2. a[i] $in cart(...).Params[i-1] for each i
func (ver *Verifier) verInFactByRightParamIsCartSet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// Check if right side is cart(...)
	cartSet, ok := asPureStmt.Params[1].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}
	if !ast.IsAtomObjAndEqualToStr(cartSet.FnHead, glob.KeywordCart) {
		return ast.NewEmptyUnknownVerRet()
	}

	obj := asPureStmt.Params[0]

	// Get cart from obj if obj = cart(...)
	objCartSet := ver.getCartSetFromObj(obj)

	// Verify dim and elements
	ret := ver.verInCartSet_DimAndElements(obj, cartSet, objCartSet, state)
	if ret.IsNotTrue() {
		return ast.NewEmptyUnknownVerRet()
	}

	return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), ret.String(), ret)
}

func (ver *Verifier) ver_In_FnFcFn_FnTT(left ast.Obj, fnFcFn *ast.FnObj, state *VerState) ast.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	// check when parameters satisfy given fnFcFn parameter requirements, then it satisfies the fn template template requirement

	leftIsInWhichFnTT := ver.Env.GetLatestFnT_GivenNameIsIn(left.String())
	if leftIsInWhichFnTT == nil {
		return ast.NewEmptyUnknownVerRet()
	}

	randomNames := []string{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomNames = append(randomNames, ver.Env.GenerateUnusedRandomName())
	}
	randomAtoms := []ast.Obj{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		randomAtoms = append(randomAtoms, ast.Atom(randomNames[i]))
	}

	uniMap := map[string]ast.Obj{}
	for i := 0; i < len(leftIsInWhichFnTT.AsFnTStruct.Params); i++ {
		uniMap[leftIsInWhichFnTT.AsFnTStruct.Params[i]] = ast.Atom(randomNames[i])
	}

	// check parameters of the left satisfies the fn template template requirement
	for i, randomName := range randomNames {
		ok, errMsg := ver.Env.CheckAtomObjNameIsValidAndAvailableThenDefineIt(randomName)
		if !ok {
			return ast.NewErrVerRet(nil).AddExtraInfo(errMsg)
		}
		ret := ver.Env.NewFactWithCheckingNameDefined(ast.NewInFactWithParamObj(ast.Atom(randomName), (fnFcFn.FnHead).(*ast.FnObj).Params[i], glob.BuiltinLine0))
		if ret.IsErr() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
		}
	}

	leftToUniFact, err := leftIsInWhichFnTT.AsFnTStruct.DeriveUniFact_WithGivenFn(left)
	if err != nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
	}

	instantiatedLeftToUniFact, err := leftToUniFact.InstantiateFact(uniMap)
	if err != nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(err.Error())
	}
	instLeftUniFactAsUniFactStmt, ok := instantiatedLeftToUniFact.(*ast.UniFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	for i := range instLeftUniFactAsUniFactStmt.Params {
		fact := ast.NewInFactWithParamObj(ast.Atom(randomNames[i]), leftIsInWhichFnTT.AsFnTStruct.ParamSets[i], glob.BuiltinLine0)
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		ret := ver.Env.NewFactWithCheckingNameDefined(fact)
		if ret.IsErr() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
		}
	}

	for i := range leftIsInWhichFnTT.AsFnTStruct.DomFacts {
		fact := leftIsInWhichFnTT.AsFnTStruct.DomFacts[i]
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		ret := ver.Env.NewFactWithCheckingNameDefined(fact)
		if ret.IsErr() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
		}
	}

	// whether return value is in ret set of fnFcFn
	fn := ast.NewFnObj(left, randomAtoms)
	verRet := ver.VerFactStmt(ast.NewInFactWithParamObj(fn, fnFcFn.Params[0], glob.BuiltinLine0), state)
	return verRet
}

func (ver *Verifier) verInFactByLeftParamIsReturnValueOfUserDefinedFn(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	fcFn, ok := asPureStmt.Params[0].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if fcFn.HasHeadInSlice([]string{glob.KeySymbolPlus, glob.KeySymbolMinus, glob.KeySymbolStar, glob.KeySymbolSlash, glob.KeySymbolPower}) {
		if asPureStmt.Params[1] == ast.Atom(glob.KeywordReal) {
			msg := fmt.Sprintf("return value of builtin arithmetic function %s is in Real", fcFn)
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
		}
		return ast.NewEmptyUnknownVerRet()
	}

	if fcFn.HasHeadInSlice([]string{glob.KeywordCount, glob.KeySymbolPercent}) {
		if asPureStmt.Params[1] == ast.Atom(glob.KeywordNatural) {
			msg := fmt.Sprintf("return value of builtin function %s is in Natural", fcFn)
			return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
		}
		return ast.NewEmptyUnknownVerRet()
	}

	setFcFnIsIn_ByItsFnT, err := ver.getRetSetOfFcFnByUsingItsFnT(fcFn)
	if err != nil {
		return ast.NewEmptyUnknownVerRet()
	}

	verRet := ver.VerFactStmt(ast.EqualFact(asPureStmt.Params[1], setFcFnIsIn_ByItsFnT), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		msg := fmt.Sprintf("return value of function %s is in its function template return set %s", fcFn, setFcFnIsIn_ByItsFnT)
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}
	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) getRetSetOfFcFnByUsingItsFnT(fcFn *ast.FnObj) (ast.Obj, error) {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, _ := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	// 此时 indexWhereLatestFnTIsGot 就是 1, FnToFnItemWhereLatestFnTIsGot 就是 f(a) 的 fnInFnTMemItem
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.Env.FindRightMostResolvedFn_Return_ResolvedIndexAndFnTMemItem(fnHeadChain_AndItSelf)

	if FnToFnItemWhereLatestFnTIsGot == nil {
		return nil, fmt.Errorf("no fn template found for %s", fcFn)
	}

	// 比如 f(a)(b,c)(e,d,f) 我们现在得到了 f(a) 的 fnTStruct，那 curParamsChainIndex 就是 2, 表示 f(a) 对应的params就是 (b,c)
	curFnTStruct := (FnToFnItemWhereLatestFnTIsGot.AsFnTStruct)
	curParamsChainIndex := indexWhereLatestFnTIsGot + 1

	// 验证 paramsChain 是否满足 fnTStruct，比如 b,c 是否满足 f(a) 的参数要求
	for curParamsChainIndex < len(fnHeadChain_AndItSelf)-1 {
		curRetSet, ok := curFnTStruct.RetSet.(*ast.FnObj)
		if !ok {
			return nil, fmt.Errorf("curRetSet is not an FcFn")
		}

		var shortRet ast.ShortRet
		// curFnTStruct, ret = ver.GetFnStructFromFnTName_CheckFnTParamsReq(curRetSet, state)
		curFnTStruct, shortRet = ver.Env.GetFnStructFromFnTName(curRetSet)
		if shortRet.IsErr() {
			return nil, fmt.Errorf(shortRet.String())
		}

		curParamsChainIndex++
	}

	uniMap := map[string]ast.Obj{}
	for i := 0; i < len(curFnTStruct.Params); i++ {
		uniMap[curFnTStruct.Params[i]] = fcFn.Params[i]
	}
	// inst return set
	instRetSet, err := curFnTStruct.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, fmt.Errorf(err.Error())
	}

	return instRetSet, nil
}

func (ver *Verifier) litNumNotInNaturalByLiteralShape(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查是否是 not x $in N 的形式
	if !ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNatural) {
		return ast.NewEmptyUnknownVerRet()
	}

	_, toEval := ver.GetValueOfSymbol(asPureStmt.Params[0])

	if !cmp.IsNumExprLitObj(toEval) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查 toEval 是否是纯数字（Atom），如果不是（有运算符），则不在 N 中
	_, isAtom := toEval.(ast.Atom)
	if !isAtom {
		// 有运算符，不是纯数字，不在 N 中
		msg := fmt.Sprintf("%s is not a pure number (has operators), so it is not in N", toEval)
		return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 检查是否有小数点
	if ast.IsObjLiterallyRationalNumber(toEval) {
		msg := fmt.Sprintf("%s has a decimal point, so it is not in N", toEval)
		return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 检查是否有负号（一元负号运算符）
	if fnObj, ok := asPureStmt.Params[0].(*ast.FnObj); ok {
		if ast.IsObjBuiltinUnaryFn(*fnObj) {
			if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
				// 有负号，不在 N 中
				msg := fmt.Sprintf("%s has a minus sign, so it is not in N", asPureStmt.Params[0])
				return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		}
	}
	// 也检查 toEval 是否有负号（如果评估后仍然是负号）
	if fnObj, ok := toEval.(*ast.FnObj); ok {
		if ast.IsObjBuiltinUnaryFn(*fnObj) {
			if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
				// 有负号，不在 N 中
				msg := fmt.Sprintf("%s has a minus sign, so it is not in N", toEval)
				return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		}
	}

	// 如果是纯数字且没有小数点，检查是否是自然数形状
	// 如果字面上就是自然数形状（比如 "5"），不能证明它不在自然数中
	if ast.IsObjLiterallyNatNumber(toEval) {
		// 字面上是自然数，不能证明它不在自然数中
		return ast.NewEmptyUnknownVerRet()
	}

	// 如果是纯数字但不是自然数形状（负数），可以证明它不在自然数中
	msg := fmt.Sprintf("%s is literally not a natural number (not in the shape of natural number)", toEval)
	return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
}

func (ver *Verifier) litNumNotInIntegerByLiteralShape(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查是否是 not x $in Z 的形式
	if !ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordInteger) {
		return ast.NewEmptyUnknownVerRet()
	}

	_, toEval := ver.GetValueOfSymbol(asPureStmt.Params[0])

	if !cmp.IsNumExprLitObj(toEval) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查 toEval 是否是纯数字（Atom），如果不是（有运算符），则不在 Z 中
	_, isAtom := toEval.(ast.Atom)
	if !isAtom {
		// 有运算符，不是纯数字，不在 Z 中
		msg := fmt.Sprintf("%s is not a pure number (has operators), so it is not in Z", toEval)
		return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 检查是否有小数点
	if ast.IsObjLiterallyRationalNumber(toEval) {
		msg := fmt.Sprintf("%s has a decimal point, so it is not in Z", toEval)
		return ver.maybeAddSuccessMsgString(state, stmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) litNumNotInNPosByLiteralShape(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查是否是 not x $in N_pos 的形式
	if !ast.IsAtomObjAndEqualToStr(asPureStmt.Params[1], glob.KeywordNPos) {
		return ast.NewEmptyUnknownVerRet()
	}

	_, toEval := ver.GetValueOfSymbol(asPureStmt.Params[0])

	if !cmp.IsNumExprLitObj(toEval) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 检查 toEval 是否是纯数字（Atom），如果不是（有运算符），则不在 N_pos 中
	_, isAtom := toEval.(ast.Atom)
	if !isAtom {
		// 有运算符，不是纯数字，不在 N_pos 中
		msg := fmt.Sprintf("%s is not a pure number (has operators), so it is not in N_pos", toEval)
		return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 检查是否有小数点
	if ast.IsObjLiterallyRationalNumber(toEval) {
		msg := fmt.Sprintf("%s has a decimal point, so it is not in N_pos", toEval)
		return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
	}

	// 检查是否有负号（一元负号运算符）
	if fnObj, ok := asPureStmt.Params[0].(*ast.FnObj); ok {
		if ast.IsObjBuiltinUnaryFn(*fnObj) {
			if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
				// 有负号，不在 N_pos 中
				msg := fmt.Sprintf("%s has a minus sign, so it is not in N_pos", asPureStmt.Params[0])
				return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		}
	}
	// 也检查 toEval 是否有负号（如果评估后仍然是负号）
	if fnObj, ok := toEval.(*ast.FnObj); ok {
		if ast.IsObjBuiltinUnaryFn(*fnObj) {
			if headAtom, ok := fnObj.FnHead.(ast.Atom); ok && string(headAtom) == glob.KeySymbolMinus {
				// 有负号，不在 N_pos 中
				msg := fmt.Sprintf("%s has a minus sign, so it is not in N_pos", toEval)
				return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
			}
		}
	}

	// 如果是纯数字且没有小数点，检查是否是正整数形状
	// 如果字面上就是正整数形状（比如 "5"），不能证明它不在正整数中
	if ast.IsObjLiterallyNPosNumber(toEval) {
		// 字面上是正整数，不能证明它不在正整数中
		return ast.NewEmptyUnknownVerRet()
	}

	// 如果是纯数字但不是正整数形状（负数、0），可以证明它不在正整数中
	msg := fmt.Sprintf("%s is literally not a positive integer (not in the shape of positive integer)", toEval)
	return ver.maybeAddSuccessMsgString(state, asPureStmt.String(), msg, ast.NewTrueVerRet(stmt, nil, ""))
}

func (ver *Verifier) verInFactByLeftIsIndexOfObjInSomeSet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	left := asPureStmt.Params[0]
	someSet := asPureStmt.Params[1]

	var leftAsFn *ast.FnObj

	if leftAsFn, ok = left.(*ast.FnObj); !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if leftAsFn.FnHead.String() != glob.KeywordObjAtIndexOpt {
		return ast.NewEmptyUnknownVerRet()
	}

	// 找到它所在的 cart
	objCartSet := ver.getCartSetFromObj(left)
	if objCartSet == nil {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(leftAsFn.Params) != 2 {
		return ast.NewEmptyUnknownVerRet()
	}

	index := leftAsFn.Params[1]
	indexAsInt, err := strconv.Atoi(string(index.(ast.Atom)))
	if err != nil {
		return ast.NewEmptyUnknownVerRet()
	}
	if indexAsInt < 1 || indexAsInt > len(objCartSet.Params) {
		return ast.NewEmptyUnknownVerRet()
	}

	// 看看在index处是不是在someSet中, index 是 整数
	indexObj := objCartSet.Params[indexAsInt-1]
	verRet := ver.VerFactStmt(ast.NewInFactWithObj(indexObj, someSet), state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verInFactByRightIsSetBuilder(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if state.isFinalRound() {
		return ast.NewEmptyUnknownVerRet()
	}

	setBuilder := ver.Env.GetSetBuilderEqualToObj(asPureStmt.Params[1])
	if setBuilder == nil {
		return ast.NewEmptyUnknownVerRet()
	}

	// nextState := state.GetAddRound()

	setBuilderStruct, err := setBuilder.ToSetBuilderStruct()
	if err != nil {
		return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
	}

	uniMap := map[string]ast.Obj{setBuilderStruct.Param: asPureStmt.Params[0]}

	// Instantiate all facts
	instFacts := []ast.FactStmt{}
	for _, fact := range setBuilderStruct.Facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return ast.NewErrVerRet(stmt).AddExtraInfo(err.Error())
		}
		instFacts = append(instFacts, instFact)
	}

	// First, verify that the element is in the parent set
	instParentSetFact := ast.NewInFactWithObj(asPureStmt.Params[0], setBuilderStruct.ParentSet)
	parentSetRet := ver.VerFactStmt(instParentSetFact, state)
	if parentSetRet.IsNotTrue() {
		return parentSetRet
	}

	// Then, verify all facts are true
	for _, fact := range instFacts {
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsNotTrue() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	return ast.NewTrueVerRet(stmt, nil, "definition of set builder")
}

func (ver *Verifier) verInFactByRightIsListSet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	listSetObj := ver.Env.GetListSetEqualToObj(asPureStmt.Params[1])
	if listSetObj == nil {
		return ast.NewEmptyUnknownVerRet()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	// 遍历 list set 的所有元素，检查是否有任何一个等于 stmt.Params[0]
	for _, item := range listSetFnObj.Params {
		equalFact := ast.NewEqualFact(asPureStmt.Params[0], item)
		verRet := ver.VerFactStmt(equalFact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			// 找到了相等的元素，返回 true
			if asPureStmt.Params[0].String() == item.String() {
				return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s $in %s, %s = %s", asPureStmt.Params[0], listSetFnObj.String(), asPureStmt.Params[1], listSetFnObj))
			}

			return ast.NewTrueVerRet(stmt, nil, fmt.Sprintf("%s $in %s, %s = %s, %s = %s", asPureStmt.Params[0], listSetFnObj.String(), asPureStmt.Params[1], listSetFnObj, item, asPureStmt.Params[0]))
		}
	}

	// 没有找到相等的元素，返回 unknown
	return ast.NewEmptyUnknownVerRet()
}

func (ver *Verifier) verInFactByLeftParamIsReturnValueOfSuperFn(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	setWhereObjIsIn, ok := asPureStmt.Params[0].(*ast.FnObj)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	switch setWhereObjIsIn.FnHead.String() {
	case glob.KeywordDim:
		return ver.VerFactStmt(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordSubsetOf), []ast.Obj{ast.Atom(glob.KeywordNPos), asPureStmt.Params[1]}, glob.BuiltinLine0), state)
	case glob.KeywordCount:
		return ver.VerFactStmt(ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordSubsetOf), []ast.Obj{ast.Atom(glob.KeywordNatural), asPureStmt.Params[1]}, glob.BuiltinLine0), state)
	default:
		return ast.NewEmptyUnknownVerRet()
	}
}

// func (ver *Verifier) verInFactByRightIsPowerSet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
// 	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
// 	if !ok {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if len(asPureStmt.Params) != 2 {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	if asFnObj, ok := asPureStmt.Params[1].(*ast.FnObj); ok {
// 		if asFnObj.FnHead.String() != glob.KeywordPowerSet || len(asFnObj.Params) != 1 {
// 			return ast.NewEmptyUnknownVerRet()
// 		}
// 	} else {
// 		return ast.NewEmptyUnknownVerRet()
// 	}

// 	randomAtom := ver.Env.GenerateUndeclaredRandomName()

// 	// 证明 forall x X: x $in X
// 	forallFact := ast.NewUniFact(
// 		[]string{randomAtom},
// 		[]ast.Obj{asPureStmt.Params[0]},
// 		[]ast.FactStmt{},
// 		[]ast.FactStmt{ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{ast.Atom(randomAtom), asPureStmt.Params[1].(*ast.FnObj).Params[0]}, glob.BuiltinLine0)},
// 		glob.BuiltinLine0,
// 	)
// 	verRet := ver.VerFactStmt(forallFact, state)

// 	return verRet
// }

func (ver *Verifier) verInFactByRightIsPowerSet(stmt ast.SpecificFactStmt, state *VerState) ast.VerRet {
	asPureStmt, ok := stmt.(*ast.PureSpecificFactStmt)
	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	if len(asPureStmt.Params) != 2 {
		return ast.NewEmptyUnknownVerRet()
	}

	var asFnObj *ast.FnObj
	if asFnObj, ok = asPureStmt.Params[1].(*ast.FnObj); ok {
		if asFnObj.FnHead.String() != glob.KeywordPowerSet {
			return ast.NewEmptyUnknownVerRet()
		}
	} else {
		return ast.NewEmptyUnknownVerRet()
	}

	randomName := ver.Env.GenerateUnusedRandomName()
	equivalentForallFact := ast.NewUniFact([]string{randomName}, []ast.Obj{asPureStmt.Params[0]}, []ast.Spec_OrFact{}, []ast.Spec_OrFact{ast.NewInFactWithObj(ast.Atom(randomName), asFnObj.Params[0])}, glob.BuiltinLine0)

	verRet := ver.VerFactStmt(equivalentForallFact, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsTrue() {
		return verRet
	}

	return ast.NewEmptyUnknownVerRet()
}
