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

type InferenceEngine struct {
	Env *Env
}

func NewInferenceEngine(env *Env) *InferenceEngine {
	return &InferenceEngine{Env: env}
}

// TODO: 好像这里的条件也不一定是互斥的，所以如果ret.IsTrue()了，也不一定要返回 true，而是应该继续尝试其他条件
func (ie *InferenceEngine) trueInFact(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	if ret := ie.trueInFactByFnTemplate(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByFnTemplateFnObj(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByCart(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByListSet(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactBySetBuilder(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByRangeOrClosedRange(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if fact.Params[1].String() == glob.KeywordNPos {
		return ie.trueInFactByNPos(fact)
	}

	return glob.NewGlobTrue("")
}

// trueInFactByFnTemplate handles a $in fnTemplate(...) case
func (ie *InferenceEngine) trueInFactByFnTemplate(fact *ast.SpecFactStmt) glob.GlobRet {
	isTemplate, ret := ie.trueInFactInFnTemplate(fact)
	if ret.IsErr() {
		return ret
	}
	if isTemplate {
		return ret
	}
	return glob.NewEmptyGlobUnknown()
}

func (ie *InferenceEngine) trueInFactByFnTemplateFnObj(fact *ast.SpecFactStmt) glob.GlobRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsFnTemplate_ObjFn(fnFn) {
		return glob.NewEmptyGlobUnknown()
	}

	fnTStruct, ok := ast.ObjFnT_To_FnTStruct(fnFn)
	if !ok {
		return glob.ErrRet(fmt.Errorf("%s is not obj type fn template", fnFn.String()))
	}

	ret := ie.Env.InsertFnInFnTT(fact.Params[0], fnTStruct)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

// trueInFactByCart handles a $in cart(...) case
// It tries both direct cart and cart from equal facts
func (ie *InferenceEngine) trueInFactByCart(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try direct cart first
	if fnObj, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordCart) {
		return ie.trueInFactInCart(fact.Params[0], fnObj)
	}

	// Try cart from equal facts
	equalObjs, ok := ie.Env.GetEqualObjs(fact.Params[1])
	if !ok || equalObjs == nil {
		return glob.NewEmptyGlobUnknown()
	}

	// Look for a cart set in the equal facts
	for _, equalObj := range *equalObjs {
		if cartAsFn, ok := equalObj.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
			return ie.trueInFactInCart(fact.Params[0], cartAsFn)
		}
	}

	return glob.NewEmptyGlobUnknown()
}

// trueInFactInCart handles postprocessing for a $in cart(...)
// It generates a[i] $in cartSet.Params[i] facts and dim(a) = len(cartSet.Params) fact
func (ie *InferenceEngine) trueInFactInCart(obj ast.Obj, cartSet *ast.FnObj) glob.GlobRet {
	// 为每个索引生成 a[i] $in cartSet.Params[i-1] 的事实（索引从1开始）
	for i := range len(cartSet.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(fmt.Sprintf("%d", index))
		// 创建索引操作 a[i]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})
		// 创建 a[i] $in cartSet.Params[i] 的事实
		inFact := ast.NewInFactWithObj(indexedObj, cartSet.Params[i])
		ret := ie.Env.NewFact(inFact)
		if ret.IsErr() {
			return ret
		}
	}
	// 添加 dim(obj) = len(cartSet.Params) 的事实
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj})
	dimValue := ast.Atom(strconv.Itoa(len(cartSet.Params)))
	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
	ret := ie.Env.NewFact(dimEqualFact)
	if ret.IsErr() {
		return ret
	}
	// 添加 is_tuple(obj) 的事实
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.BuiltinLine)
	ret = ie.Env.NewFact(isTupleFact)
	if ret.IsErr() {
		return ret
	}
	return glob.NewGlobTrue("")
}

func (ie *InferenceEngine) trueInFactInFnTemplate(fact *ast.SpecFactStmt) (bool, glob.GlobRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.NewGlobTrue("")
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.NewGlobTrue("")
	}

	def := ie.Env.GetFnTemplateDef_KeyIsObjHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.NewGlobTrue("")
	}

	fnTNoName, ok, ret := ie.Env.getInstantiatedFnTTOfFnObj(fact.Params[1].(*ast.FnObj))
	if ret.IsErr() {
		return false, ret
	}
	if !ok {
		return false, glob.NewGlobTrue("")
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, glob.ErrRet(err)
	}

	ret = ie.Env.NewFact(derivedFact)
	if ret.IsErr() {
		return false, ret
	}

	ret = ie.Env.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, ret
	}

	return true, glob.NewGlobTrue("")
}

// trueInFactInListSet handles postprocessing for a $in listSet(...)
// It generates an or fact indicating that the left param equals one of the listSetFnObj params
func (ie *InferenceEngine) trueInFactInListSet(obj ast.Obj, listSetFnObj *ast.FnObj) glob.GlobRet {
	// 用所有的param做一个or出来，说明left等于其中的一个
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, param}, glob.BuiltinLine))
	}
	ret := ie.Env.NewFact(orFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (ie *InferenceEngine) trueInFactByListSet(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try to get listSet, either directly or from equal facts
	listSetObj := ie.Env.GetListSetEqualToObj(fact.Params[1])
	if listSetObj == nil {
		return glob.NewEmptyGlobUnknown()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected list set to be FnObj, got %T", listSetObj))
	}

	return ie.trueInFactInListSet(fact.Params[0], listSetFnObj)
}

func (ie *InferenceEngine) trueInFactBySetBuilder(fact *ast.SpecFactStmt) glob.GlobRet {
	setBuilderObj := ie.Env.GetSetBuilderEqualToObj(fact.Params[1])
	if setBuilderObj == nil {
		return glob.NewEmptyGlobUnknown()
	}

	return ie.trueInFactInSetBuilder(fact.Params[0], setBuilderObj)
}

func (ie *InferenceEngine) trueInFactInSetBuilder(obj ast.Obj, setBuilderObj *ast.FnObj) glob.GlobRet {
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
	ret := ie.Env.NewFact(inParentSetFact)
	if ret.IsErr() {
		return glob.ErrRet(err)
	}

	// intentional facts are true
	for _, fact := range instFacts {
		ret := ie.Env.NewFact(fact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

func (ie *InferenceEngine) trueInFactByRangeOrClosedRange(fact *ast.SpecFactStmt) glob.GlobRet {
	// Check if the second parameter is a range or closed_range function call
	if !ast.ObjIsRangeOrClosedRangeWith2Params(fact.Params[1]) {
		return glob.NewEmptyGlobUnknown()
	}

	derivedFacts := []string{}

	obj := fact.Params[0]
	rangeOrClosedRange := fact.Params[1].(*ast.FnObj)
	left := rangeOrClosedRange.Params[0]
	right := rangeOrClosedRange.Params[1]
	isRange := rangeOrClosedRange.FnHead.String() == glob.KeywordRange

	// in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret := ie.Env.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inZFact.String())

	// Generate x >= left
	greaterEqualLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, left}, fact.Line)
	ret = ie.Env.storeSpecFactInMem(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterEqualLeftFact.String())
	ret = ie.Env.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	if isRange {
		// range: generate x < right
		lessRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, right}, fact.Line)
		ret = ie.Env.storeSpecFactInMem(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		derivedFacts = append(derivedFacts, lessRightFact.String())
		ret = ie.Env.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
			derivedFacts = append(derivedFacts, ret.GetMsgs()...)
		}
	} else {
		// closed_range: generate x <= right
		lessEqualRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{obj, right}, fact.Line)
		ret = ie.Env.storeSpecFactInMem(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
		derivedFacts = append(derivedFacts, lessEqualRightFact.String())
		ret = ie.Env.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
		if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
			derivedFacts = append(derivedFacts, ret.GetMsgs()...)
		}
	}

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrueWithMsgs(derivedFacts)
	}
	return glob.NewGlobTrue("")
}

func (ie *InferenceEngine) trueInFactByNPos(fact *ast.SpecFactStmt) glob.GlobRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in N
	inNFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordNatural))
	ret := ie.Env.storeSpecFactInMem(inNFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inNFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.Env.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.Env.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine)
	ret = ie.Env.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterThanZeroFact.String())
	ret = ie.Env.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	// x >= 1
	greaterEqualOneFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("1")}, glob.BuiltinLine)
	ret = ie.Env.storeSpecFactInMem(greaterEqualOneFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterEqualOneFact.String())

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrueWithMsgs(derivedFacts)
	}
	return glob.NewGlobTrue("")
}
