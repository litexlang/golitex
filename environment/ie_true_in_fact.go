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

// trueInFact handles postprocessing for true $in facts (x $in S).
// It performs various inferences based on the type of set S:
//
// Inference types:
//  1. FnTemplate inference: If S is a function template, derives a universal fact
//     and stores the function-template relationship
//  2. FnTemplateFnObj inference: If S is an object-type function template function,
//     inserts the function into the function template table
//  3. Cart inference: If S is a cartesian product cart(S1, S2, ..., Sn), generates:
//     - a[i] $in Si for each i (indexed membership facts)
//     - dim(a) = n (dimension fact)
//     - is_tuple(a) (tuple type fact)
//  4. ListSet inference: If S is a list set {e1, e2, ..., en}, generates:
//     - An OR fact: x = e1 or x = e2 or ... or x = en
//  5. SetBuilder inference: If S is a set builder {x in T: P(x)}, generates:
//     - x $in T (parent set membership)
//     - P(x) (all intentional facts from the builder)
//  6. Range/ClosedRange inference: If S is range(a, b) or closed_range(a, b), generates:
//     - x $in Z (integer membership)
//     - x >= a (lower bound)
//     - x < b (for range) or x <= b (for closed_range)
//     - Additional derived facts from comparison postprocessing
//  7. NPos inference: If S is NPos (positive natural numbers), generates:
//     - x $in N, x $in Q, x $in R (number type memberships)
//     - x > 0, x >= 1 (positivity facts)
//     - Additional derived facts from comparison postprocessing
//
// TODO: The conditions are not necessarily mutually exclusive, so if ret.IsTrue(),
// we might want to continue trying other conditions instead of returning immediately.
func (ie *InferEngine) trueInFact(fact *ast.SpecFactStmt) glob.GlobRet {
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

	return glob.NewEmptyGlobTrue()
}

// trueInFactByFnTemplate handles inference for x $in fnTemplate(...)
// Inference: Derives a universal fact from the function template definition
// and stores the function-template satisfaction relationship
func (ie *InferEngine) trueInFactByFnTemplate(fact *ast.SpecFactStmt) glob.GlobRet {
	isTemplate, ret := ie.trueInFactInFnTemplate(fact)
	if ret.IsErr() {
		return ret
	}
	if isTemplate {
		return ret
	}
	return glob.NewEmptyGlobUnknown()
}

// trueInFactByFnTemplateFnObj handles inference for x $in fnTemplateFnObj
// Inference: Inserts the function x into the function template table
func (ie *InferEngine) trueInFactByFnTemplateFnObj(fact *ast.SpecFactStmt) glob.GlobRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsFnTemplate_ObjFn(fnFn) {
		return glob.NewEmptyGlobUnknown()
	}

	fnTStruct, ok := ast.ObjFnT_To_FnTStruct(fnFn)
	if !ok {
		return glob.ErrRet(fmt.Errorf("%s is not obj type fn template", fnFn.String()))
	}

	ret := ie.EnvMgr.InsertFnInFnTT(fact.Params[0], fnTStruct)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// trueInFactByCart handles inference for x $in cart(S1, S2, ..., Sn)
// It tries both direct cart and cart from equal facts
// Inference: If x is in a cartesian product, then each component of x is in the corresponding set
func (ie *InferEngine) trueInFactByCart(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try direct cart first
	if fnObj, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordCart) {
		return ie.trueInFactInCart(fact.Params[0], fnObj)
	}

	// Try cart from equal facts
	equalObjs, ok := ie.EnvMgr.GetEqualObjs(fact.Params[1])
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

// trueInFactInCart handles inference for obj $in cart(S1, S2, ..., Sn)
// Inference generates:
//   - a[i] $in Si for each i (each component is in the corresponding set)
//   - dim(a) = n (dimension equals the number of sets)
//   - is_tuple(a) (the object is a tuple)
func (ie *InferEngine) trueInFactInCart(obj ast.Obj, cartSet *ast.FnObj) glob.GlobRet {
	// 为每个索引生成 a[i] $in cartSet.Params[i-1] 的事实（索引从1开始）
	for i := range len(cartSet.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(fmt.Sprintf("%d", index))
		// 创建索引操作 a[i]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordIndexOpt), []ast.Obj{obj, indexObj})
		// 创建 a[i] $in cartSet.Params[i] 的事实
		inFact := ast.NewInFactWithObj(indexedObj, cartSet.Params[i])
		ret := ie.EnvMgr.NewFactWithAtomsDefined(inFact)
		if ret.IsErr() {
			return ret
		}
	}
	// 添加 dim(obj) = len(cartSet.Params) 的事实
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj})
	dimValue := ast.Atom(strconv.Itoa(len(cartSet.Params)))
	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
	ret := ie.EnvMgr.NewFactWithAtomsDefined(dimEqualFact)
	if ret.IsErr() {
		return ret
	}
	// 添加 is_tuple(obj) 的事实
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.BuiltinLine)
	ret = ie.EnvMgr.NewFactWithAtomsDefined(isTupleFact)
	if ret.IsErr() {
		return ret
	}
	return glob.NewEmptyGlobTrue()
}

func (ie *InferEngine) trueInFactInFnTemplate(fact *ast.SpecFactStmt) (bool, glob.GlobRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.NewEmptyGlobTrue()
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.NewEmptyGlobTrue()
	}

	def := ie.EnvMgr.GetFnTemplateDef_KeyIsObjHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.NewEmptyGlobTrue()
	}

	fnTNoName, ok, ret := ie.EnvMgr.getInstantiatedFnTTOfFnObj(fact.Params[1].(*ast.FnObj))
	if ret.IsErr() {
		return false, ret
	}
	if !ok {
		return false, glob.NewEmptyGlobTrue()
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, glob.ErrRet(err)
	}

	ret = ie.EnvMgr.NewFactWithAtomsDefined(derivedFact)
	if ret.IsErr() {
		return false, ret
	}

	ret = ie.EnvMgr.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, ret
	}

	return true, glob.NewEmptyGlobTrue()
}

// trueInFactInListSet handles inference for obj $in listSet(e1, e2, ..., en)
// Inference: Generates an OR fact indicating that obj equals one of the list set elements
// Result: obj = e1 or obj = e2 or ... or obj = en
func (ie *InferEngine) trueInFactInListSet(obj ast.Obj, listSetFnObj *ast.FnObj) glob.GlobRet {
	// 用所有的param做一个or出来，说明left等于其中的一个
	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, param}, glob.BuiltinLine))
	}
	ret := ie.EnvMgr.NewFactWithAtomsDefined(orFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// trueInFactByListSet handles inference for x $in listSet(...)
// It tries to get the listSet either directly or from equal facts
// Inference: If x is in a finite list set, then x equals one of the elements
func (ie *InferEngine) trueInFactByListSet(fact *ast.SpecFactStmt) glob.GlobRet {
	// Try to get listSet, either directly or from equal facts
	listSetObj := ie.EnvMgr.GetListSetEqualToObj(fact.Params[1])
	if listSetObj == nil {
		return glob.NewEmptyGlobUnknown()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.ErrRet(fmt.Errorf("expected list set to be FnObj, got %T", listSetObj))
	}

	return ie.trueInFactInListSet(fact.Params[0], listSetFnObj)
}

// trueInFactBySetBuilder handles inference for x $in {y in T: P(y)}
// Inference: If x is in a set builder, then x is in the parent set T and satisfies all intentional facts P(x)
func (ie *InferEngine) trueInFactBySetBuilder(fact *ast.SpecFactStmt) glob.GlobRet {
	setBuilderObj := ie.EnvMgr.GetSetBuilderEqualToObj(fact.Params[1])
	if setBuilderObj == nil {
		return glob.NewEmptyGlobUnknown()
	}

	return ie.trueInFactInSetBuilder(fact.Params[0], setBuilderObj)
}

// trueInFactInSetBuilder handles inference for obj $in {param in parentSet: facts}
// Inference generates:
//   - obj $in parentSet (membership in parent set)
//   - All instantiated intentional facts from the set builder
func (ie *InferEngine) trueInFactInSetBuilder(obj ast.Obj, setBuilderObj *ast.FnObj) glob.GlobRet {
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
	ret := ie.EnvMgr.NewFactWithAtomsDefined(inParentSetFact)
	if ret.IsErr() {
		return glob.ErrRet(err)
	}

	// intentional facts are true
	for _, fact := range instFacts {
		ret := ie.EnvMgr.NewFactWithAtomsDefined(fact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// trueInFactByRangeOrClosedRange handles inference for x $in range(a, b) or x $in closed_range(a, b)
// Inference generates:
//   - x $in Z (integer membership)
//   - x >= a (lower bound)
//   - x < b (for range) or x <= b (for closed_range)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, etc.)
func (ie *InferEngine) trueInFactByRangeOrClosedRange(fact *ast.SpecFactStmt) glob.GlobRet {
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
	ret := ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inZFact.String())

	// Generate x >= left
	greaterEqualLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, left}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterEqualLeftFact.String())
	ret = ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	if isRange {
		// range: generate x < right
		lessRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		derivedFacts = append(derivedFacts, lessRightFact.String())
		ret = ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
			derivedFacts = append(derivedFacts, ret.GetMsgs()...)
		}
	} else {
		// closed_range: generate x <= right
		lessEqualRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
		derivedFacts = append(derivedFacts, lessEqualRightFact.String())
		ret = ie.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(lessEqualRightFact)
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
	return glob.NewEmptyGlobTrue()
}

// trueInFactByNPos handles inference for x $in NPos (positive natural numbers)
// Inference generates:
//   - x $in N, x $in Q, x $in R (number type memberships)
//   - x > 0, x >= 1 (positivity facts)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByNPos(fact *ast.SpecFactStmt) glob.GlobRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in N
	inNFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordNatural))
	ret := ie.EnvMgr.storeSpecFactInMem(inNFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inNFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterThanZeroFact.String())
	ret = ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	// x >= 1
	greaterEqualOneFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("1")}, glob.BuiltinLine)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualOneFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, greaterEqualOneFact.String())

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrueWithMsgs(derivedFacts)
	}
	return glob.NewEmptyGlobTrue()
}
