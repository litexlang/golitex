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

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	// Try different postprocessing strategies in order
	if ret := e.inFactPostProcess_TrySetFnRetValue(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryFnTemplate(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryFnTemplateFcFn(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := e.inFactPostProcess_TryCart(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

// inFactPostProcess_TrySetFnRetValue handles a $in setFn(...) case
func (e *Env) inFactPostProcess_TrySetFnRetValue(fact *ast.SpecFactStmt) glob.GlobRet {
	def := e.GetSetFnRetValue(fact.Params[1])
	if def == nil {
		return glob.NewGlobUnknown("")
	}
	return e.inFactPostProcess_InSetFnRetValue(fact, def)
}

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
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.InnerGenLine)
	ret = e.NewFact(isTupleFact)
	if ret.IsErr() {
		return ret
	}
	return glob.TrueRet("")
}

func (e *Env) inFactPostProcess_InSetFnRetValue(fact *ast.SpecFactStmt, def *ast.HaveSetFnStmt) glob.GlobRet {
	inFactRightParamAsFcFnPt, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range def.DefHeader.Params {
		uniMap[param] = inFactRightParamAsFcFnPt.Params[i]
	}

	defToIntensionalSetStmt := def.ToIntensionalSetStmt()
	instantiated, err := defToIntensionalSetStmt.InstantiateFact(uniMap)
	if err != nil {
		return glob.ErrRet(err)
	}

	ret := e.NewFact(instantiated)
	if ret.IsErr() {
		return ret
	}

	return glob.TrueRet("")
}

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
	inSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{fact.Params[0], ast.Atom(glob.KeywordSet)}, glob.InnerGenLine)
	ret := e.NewFact(inSetFact)
	if ret.IsErr() {
		return ret
	}

	// 让 $is_cart(x) 成立
	isCartFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsCart), []ast.Obj{fact.Params[0]}, glob.InnerGenLine)
	ret = e.NewFact(isCartFact)
	if ret.IsErr() {
		return ret
	}

	// dim(x) = len(cart.Params)
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordSetDim), []ast.Obj{fact.Params[0]})
	dimValue := ast.Atom(strconv.Itoa(len(cart.Params)))
	dimEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{dimFn, dimValue}, glob.InnerGenLine)
	ret = e.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}

	// proj(x, i+1) = cart.Params[i] for each i
	for i, cartParam := range cart.Params {
		projFn := ast.NewFnObj(ast.Atom(glob.KeywordProj), []ast.Obj{fact.Params[0], ast.Atom(strconv.Itoa(i + 1))})
		projEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{projFn, cartParam}, glob.InnerGenLine)
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

	// If obj is in ObjFromCartSetMem, update EqualTo; otherwise create new entry
	objStr := obj.String()
	if item, exists := e.ObjFromCartSetMem[objStr]; exists {
		// Update EqualTo
		item.EqualToOrNil = tuple
		e.ObjFromCartSetMem[objStr] = item
	} else {
		// Create new entry with empty CartSet (will be set when obj in cart(...) is processed)
		e.ObjFromCartSetMem[objStr] = ObjFromCartSetMemItem{
			CartSetOrNil: nil, // Empty CartSet, will be updated later
			EqualToOrNil: tuple,
		}
	}

	return glob.TrueRet("")
}
