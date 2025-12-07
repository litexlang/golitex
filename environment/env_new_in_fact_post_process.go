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
	parser "golitex/parser"
	"strconv"
)

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	// Try different postprocessing strategies in order
	// if ret := e.inFactPostProcess_TrySetFnRetValue(fact); ret.IsTrue() || ret.IsErr() {
	// 	return ret
	// }

	if ret := e.inFactPostProcess_TryFnTemplate(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryFnTemplateFcFn(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryCart(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryEnumSet(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryIntensionalSet(fact); ret.IsTrue() || ret.IsErr() {
		return ret
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

// inFactPostProcess_TryFnTemplateFcFn handles a $in fnTemplate_FcFn case
func (e *Env) inFactPostProcess_TryFnTemplateFcFn(fact *ast.SpecFactStmt) glob.GlobRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsFnTemplate_FcFn(fnFn) {
		return glob.NewGlobUnknown("")
	}

	fnTStruct, ok := ast.FcFnT_To_FnTStruct(fnFn)
	if !ok {
		return glob.ErrRet(fmt.Errorf("%s is not fcFn type fn template", fnFn.String()))
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
	equalFcs, ok := e.GetEqualFcs(fact.Params[1])
	if !ok || equalFcs == nil {
		return glob.NewGlobUnknown("")
	}

	// Look for a cart set in the equal facts
	for _, equalFc := range *equalFcs {
		if cartAsFn, ok := equalFc.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
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
		inFact := ast.NewInFactWithFc(indexedObj, cartSet.Params[i])
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

// func (e *Env) inFactPostProcess_InSetFnRetValue(fact *ast.SpecFactStmt, def *ast.HaveSetFnStmt) glob.GlobRet {
// 	inFactRightParamAsFcFnPt, ok := fact.Params[1].(*ast.FnObj)
// 	if !ok {
// 		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
// 	}

// 	uniMap := map[string]ast.Obj{}
// 	for i, param := range def.DefHeader.Params {
// 		uniMap[param] = inFactRightParamAsFcFnPt.Params[i]
// 	}

// 	defToIntensionalSetStmt := def.ToIntensionalSetStmt()
// 	instantiated, err := defToIntensionalSetStmt.InstantiateFact(uniMap)
// 	if err != nil {
// 		return glob.ErrRet(err)
// 	}

// 	ret := e.NewFact(instantiated)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	return glob.TrueRet("")
// }

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, glob.GlobRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.TrueRet("")
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsFcFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.TrueRet("")
	}

	def := e.GetFnTemplateDef_KeyIsFcHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.TrueRet("")
	}

	fnTNoName, ok, ret := e.getInstantiatedFnTTOfFcFn(fact.Params[1].(*ast.FnObj))
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

	// x $in set
	inSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fact.Params[0], ast.Atom(glob.KeywordSet)}, glob.BuiltinLine)
	ret := e.NewFact(inSetFact)
	if ret.IsErr() {
		return ret
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.BuiltinLine)
	ret = e.NewFact(isCartFact)
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

// inFactPostProcess_InEnumSet handles postprocessing for a $in enumset(...)
// It generates an or fact indicating that the left param equals one of the enumset params
func (e *Env) inFactPostProcess_InEnumSet(obj ast.Obj, enumSet *ast.FnObj) glob.GlobRet {
	// 用所有的param做一个or出来，说明left等于其中的一个
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range enumSet.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, param}, glob.BuiltinLine))
	}
	ret := e.NewFact(orFact)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_TryEnumSet(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try to get enumset, either directly or from equal facts
	enumSetObj := e.GetObjEnumSet(fact.Params[1])
	if enumSetObj == nil {
		return glob.NewGlobUnknown("")
	}

	enumSet, ok := enumSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected enum set to be FnObj, got %T", enumSetObj))
	}

	return e.inFactPostProcess_InEnumSet(fact.Params[0], enumSet)
}

func (e *Env) inFactPostProcess_TryIntensionalSet(fact *ast.SpecFactStmt) glob.GlobRet {
	intensionalSetObj := e.GetObjIntensionalSet(fact.Params[1])
	if intensionalSetObj == nil {
		return glob.NewGlobUnknown("")
	}

	intensionalSet, ok := intensionalSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected intensional set to be FnObj, got %T", intensionalSetObj))
	}

	return e.inFactPostProcess_InIntensionalSet(fact.Params[0], intensionalSet)
}

func (e *Env) inFactPostProcess_InIntensionalSet(obj ast.Obj, intensionalSet *ast.FnObj) glob.GlobRet {
	paramAsString, parentSet, facts, err := parser.GetParamParentSetFactsFromIntensionalSet(intensionalSet)
	if err != nil {
		return glob.ErrRet(err)
	}

	uniMap := map[string]ast.Obj{paramAsString: obj}

	instFacts := []ast.FactStmt{}

	for _, fact := range facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}
		instFacts = append(instFacts, instFact)
	}

	// in parent set
	inParentSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{obj, parentSet}, glob.BuiltinLine)
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
