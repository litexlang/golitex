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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

// TODO: 好像这里的条件也不一定是互斥的，所以如果ret.IsTrue()了，也不一定要返回 true，而是应该继续尝试其他条件
func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	if ret := e.inFactPostProcess_TryFnTemplate(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryFnTemplateFnObj(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryCart(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryListSet(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TrySetBuilder(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryRangeOrClosedRange(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if fact.Params[1].String() == glob.KeywordNPos {
		return e.inFactPostProcess_TryNPos(fact)
	}

	return glob.TrueRet("")
}

// inFactPostProcess_TrySetFnRetValue handles a $in setFn(...) case
// func (e *Env) inFactPostProcess_TrySetFnRetValue(fact *ast.SpecFactStmt) glob.GlobRet {
// 	def := e.GetSetFnRetValue(fact.Params[1])
// 	if def == nil {
// 		return glob.NewGlobUnknown("")
// 	}
// 	return e.inFactPostProcess_InSetFnRetValue(fact, def)
// }

// inFactPostProcess_TryFnTemplate handles a $in fnTemplate(...) case
func (e *Env) inFactPostProcess_TryFnTemplate(fact *ast.SpecFactStmt) glob.GlobRet {
	isTemplate, ret := e.inFactPostProcess_InFnTemplate(fact)
	if ret.IsErr() {
		return ret
	}
	if isTemplate {
		return ret
	}
	return glob.NewGlobUnknown("")
}

func (e *Env) inFactPostProcess_TryFnTemplateFnObj(fact *ast.SpecFactStmt) glob.GlobRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsFnTemplate_ObjFn(fnFn) {
		return glob.NewGlobUnknown("")
	}

	fnTStruct, ok := ast.ObjFnT_To_FnTStruct(fnFn)
	if !ok {
		return glob.ErrRet(fmt.Errorf("%s is not obj type fn template", fnFn.String()))
	}

	ret := e.InsertFnInFnTT(fact.Params[0], fnTStruct)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

// inFactPostProcess_TryCart handles a $in cart(...) case
// It tries both direct cart and cart from equal facts
func (e *Env) inFactPostProcess_TryCart(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try direct cart first
	if fnObj, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordCart) {
		return e.inFactPostProcess_InCart(fact.Params[0], fnObj)
	}

	// Try cart from equal facts
	equalObjs, ok := e.GetEqualObjs(fact.Params[1])
	if !ok || equalObjs == nil {
		return glob.NewGlobUnknown("")
	}

	// Look for a cart set in the equal facts
	for _, equalObj := range *equalObjs {
		if cartAsFn, ok := equalObj.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
			return e.inFactPostProcess_InCart(fact.Params[0], cartAsFn)
		}
	}

	return glob.NewGlobUnknown("")
}

// inFactPostProcess_InCart handles postprocessing for a $in cart(...)
// It generates a[i] $in cartSet.Params[i] facts and dim(a) = len(cartSet.Params) fact
func (e *Env) inFactPostProcess_InCart(obj ast.Obj, cartSet *ast.FnObj) glob.GlobRet {
	// 为每个索引生成 a[i] $in cartSet.Params[i-1] 的事实（索引从1开始）
	for i := range len(cartSet.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(fmt.Sprintf("%d", index))
		// 创建索引操作 a[i]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})
		// 创建 a[i] $in cartSet.Params[i] 的事实
		inFact := ast.NewInFactWithObj(indexedObj, cartSet.Params[i])
		ret := e.NewFact(inFact)
		if ret.IsErr() {
			return ret
		}
	}
	// 添加 dim(obj) = len(cartSet.Params) 的事实
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj})
	dimValue := ast.Atom(strconv.Itoa(len(cartSet.Params)))
	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
	ret := e.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}
	// 添加 is_tuple(obj) 的事实
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.BuiltinLine)
	ret = e.NewFact(isTupleFact)
	if ret.IsErr() {
		return ret
	}
	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, glob.GlobRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.TrueRet("")
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.TrueRet("")
	}

	def := e.GetFnTemplateDef_KeyIsObjHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.TrueRet("")
	}

	fnTNoName, ok, ret := e.getInstantiatedFnTTOfFnObj(fact.Params[1].(*ast.FnObj))
	if ret.IsErr() {
		return false, ret
	}
	if !ok {
		return false, glob.TrueRet("")
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, glob.ErrRet(err)
	}

	ret = e.NewFact(derivedFact)
	if ret.IsErr() {
		return false, ret
	}

	ret = e.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, ret
	}

	return true, glob.TrueRet("")
}

// 传入 x = cart(x1, x2, ..., xn)
func (e *Env) equalFactPostProcess_cart(fact *ast.SpecFactStmt) glob.GlobRet {
	cart, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected cart to be FnObj, got %T", fact.Params[1]))
	}

	// // x $in set
	// inSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fact.Params[0], ast.Atom(glob.KeywordSet)}, glob.BuiltinLine)
	// ret := e.NewFact(inSetFact)
	// if ret.IsErr() {
	// 	return ret
	// }

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.BuiltinLine)
	ret := e.NewFact(isCartFact)
	if ret.IsErr() {
		return ret
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.BuiltinLine)
	ret = e.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.BuiltinLine)
		ret = e.NewFact(projEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}

// 传入 obj 和 tuple，obj = tuple，左边是被赋值的对象，右边是 tuple
func (e *Env) equalFactPostProcess_tuple(obj ast.Obj, tupleObj ast.Obj) glob.GlobRet {
	tuple, ok := tupleObj.(*ast.FnObj)
	if !ok || !ast.IsTupleFnObj(tuple) {
		return glob.ErrRet(fmt.Errorf("expected tuple to be a tuple object, got %T", tupleObj))
	}

	// 让 obj 的每一位对应等于 tuple 的每一位
	for i := range len(tuple.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(strconv.Itoa(index))

		// 创建索引操作: obj[index]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})

		// 创建相等事实: obj[index] = tuple[i]
		indexEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{indexedObj, tuple.Params[i]}, glob.BuiltinLine)
		ret := e.NewFact(indexEqualFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}

// 处理 tuple = tuple 的情况，让每一位相等
func (e *Env) equalFactPostProcess_tupleTuple(leftTuple *ast.FnObj, rightTuple *ast.FnObj) glob.GlobRet {
	// 如果两个 tuple 的长度不同，返回错误
	if len(leftTuple.Params) != len(rightTuple.Params) {
		return glob.ErrRet(fmt.Errorf("tuple length mismatch: left has %d elements, right has %d elements", len(leftTuple.Params), len(rightTuple.Params)))
	}

	// 让每一位相等
	for i := range len(leftTuple.Params) {
		equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{leftTuple.Params[i], rightTuple.Params[i]}, glob.BuiltinLine)
		ret := e.NewFact(equalFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}

// equalFactPostProcess_tupleEquality 处理 tuple 相等的情况
// 包括: (.., …) = (.., ..), a = (.., ..), (.., ..) = a
func (e *Env) equalFactPostProcess_tupleEquality(left ast.Obj, right ast.Obj) glob.GlobRet {
	leftTuple, leftIsTuple := left.(*ast.FnObj)
	rightTuple, rightIsTuple := right.(*ast.FnObj)

	if leftIsTuple && rightIsTuple && ast.IsTupleFnObj(leftTuple) && ast.IsTupleFnObj(rightTuple) {
		// 处理 tuple = tuple 的情况，让每一位相等
		return e.equalFactPostProcess_tupleTuple(leftTuple, rightTuple)
	} else if rightIsTuple && ast.IsTupleFnObj(rightTuple) {
		// 如果右边是 tuple，左边是对象: a = (1, 2, ..)
		return e.equalFactPostProcess_tuple(left, right)
	} else if leftIsTuple && ast.IsTupleFnObj(leftTuple) {
		// 如果左边是 tuple，右边是对象: (1, 2, ..) = a
		return e.equalFactPostProcess_tuple(right, left)
	}

	return glob.TrueRet("")
}

// equalFactPostProcess_listSetEquality 处理 x = {1, 2, 3} 的情况
// 如果右边是 list set（直接或通过 equal facts），则创建一个 or fact，表示 x 等于 list set 中的某一个元素
func (e *Env) equalFactPostProcess_listSetEquality(left ast.Obj, right ast.Obj) glob.GlobRet {
	// 尝试获取 list set（可能是直接的，也可能是通过 equal facts 得到的）
	listSetObj := e.GetListSetEqualToObj(right)
	if listSetObj == nil {
		return glob.TrueRet("")
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected list set to be FnObj, got %T", listSetObj))
	}

	// 创建一个 or fact，表示 left 等于 list set 中的某一个元素
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{left, param}, glob.BuiltinLine))
	}
	ret := e.NewFact(orFact)
	if ret.IsErr() {
		return ret
	}

	// count(a) = len
	countFn := ast.NewFnObj(ast.Atom(glob.KeywordCount), []ast.Obj{left})
	countValue := ast.Atom(strconv.Itoa(len(listSetFnObj.Params)))
	countEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{countFn, countValue}, glob.BuiltinLine)
	ret = e.NewFact(countEqualFact)
	if ret.IsErr() {
		return ret
	}

	// is finite set
	isFiniteFact := ast.NewIsAFiniteSetFact(left, glob.BuiltinLine)
	return e.NewFact(isFiniteFact)
}

// inFactPostProcess_InListSet handles postprocessing for a $in listSet(...)
// It generates an or fact indicating that the left param equals one of the listSetFnObj params
func (e *Env) inFactPostProcess_InListSet(obj ast.Obj, listSetFnObj *ast.FnObj) glob.GlobRet {
	// 用所有的param做一个or出来，说明left等于其中的一个
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, param}, glob.BuiltinLine))
	}
	ret := e.NewFact(orFact)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_TryListSet(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try to get listSet, either directly or from equal facts
	listSetObj := e.GetListSetEqualToObj(fact.Params[1])
	if listSetObj == nil {
		return glob.NewGlobUnknown("")
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected list set to be FnObj, got %T", listSetObj))
	}

	return e.inFactPostProcess_InListSet(fact.Params[0], listSetFnObj)
}

func (e *Env) inFactPostProcess_TrySetBuilder(fact *ast.SpecFactStmt) glob.GlobRet {
	setBuilderObj := e.GetSetBuilderEqualToObj(fact.Params[1])
	if setBuilderObj == nil {
		return glob.NewGlobUnknown("")
	}

	return e.inFactPostProcess_InSetBuilder(fact.Params[0], setBuilderObj)
}

func (e *Env) inFactPostProcess_InSetBuilder(obj ast.Obj, setBuilderObj *ast.FnObj) glob.GlobRet {
	setBuilderStruct, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(err)
	}

	uniMap := map[string]ast.Obj{setBuilderStruct.Param: obj}

	instFacts := []ast.FactStmt{}

	for _, fact := range setBuilderStruct.Facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}
		instFacts = append(instFacts, instFact)
	}

	// in parent set
	inParentSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{obj, setBuilderStruct.ParentSet}, glob.BuiltinLine)
	ret := e.NewFact(inParentSetFact)
	if ret.IsErr() {
		return glob.ErrRet(err)
	}

	// intentional facts are true
	for _, fact := range instFacts {
		ret := e.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_TryRangeOrClosedRange(fact *ast.SpecFactStmt) glob.GlobRet {
	// Check if the second parameter is a range or closed_range function call
	if !ast.ObjIsRangeOrClosedRangeWith2Params(fact.Params[1]) {
		return glob.NewGlobUnknown("")
	}

	obj := fact.Params[0]
	rangeOrClosedRange := fact.Params[1].(*ast.FnObj)
	left := rangeOrClosedRange.Params[0]
	right := rangeOrClosedRange.Params[1]
	isRange := rangeOrClosedRange.FnHead.String() == glob.KeywordRange

	// in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret := e.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return ret
	}

	// Generate x >= left
	greaterEqualLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, left}, fact.Line)
	ret = e.storeSpecFactInMem(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	ret = e.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}

	if isRange {
		// range: generate x < right
		lessRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, right}, fact.Line)
		ret = e.storeSpecFactInMem(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		ret = e.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessRightFact)
		if ret.IsErr() {
			return ret
		}
	} else {
		// closed_range: generate x <= right
		lessEqualRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{obj, right}, fact.Line)
		ret = e.storeSpecFactInMem(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
		ret = e.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_TryNPos(fact *ast.SpecFactStmt) glob.GlobRet {
	obj := fact.Params[0]

	// x $in N
	inNFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordNatural))
	ret := e.storeSpecFactInMem(inNFact)
	if ret.IsErr() {
		return ret
	}

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = e.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = e.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine)
	ret = e.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	ret = e.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x >= 1
	greaterEqualOneFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("1")}, glob.BuiltinLine)
	ret = e.storeSpecFactInMem(greaterEqualOneFact)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}
