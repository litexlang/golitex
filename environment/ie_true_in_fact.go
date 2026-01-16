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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (ie *InferEngine) trueInFact(fact *ast.SpecFactStmt) *glob.ShortRet {
	if len(fact.Params) != 2 {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact)})
	}

	if ret := ie.trueInFactByNamedFnSet(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByAnonymousFnSetObj(fact); ret.IsTrue() || ret.IsErr() {
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

	if ret := ie.trueInFactBySetOperations(fact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if fact.Params[1].String() == glob.KeywordNatural {
		return ie.trueInFactByN(fact)
	}

	if fact.Params[1].String() == glob.KeywordNPos {
		return ie.trueInFactByNPos(fact)
	}

	if fact.Params[1].String() == glob.KeywordRPos {
		return ie.trueInFactByRPos(fact)
	}

	if fact.Params[1].String() == glob.KeywordRNeg {
		return ie.trueInFactByRNeg(fact)
	}

	if fact.Params[1].String() == glob.KeywordZNeg {
		return ie.trueInFactByZNeg(fact)
	}

	if fact.Params[1].String() == glob.KeywordQNeg {
		return ie.trueInFactByQNeg(fact)
	}

	if fact.Params[1].String() == glob.KeywordQPos {
		return ie.trueInFactByQPos(fact)
	}

	if fact.Params[1].String() == glob.KeywordRNot0 {
		return ie.trueInFactByRNot0(fact)
	}

	if fact.Params[1].String() == glob.KeywordZNot0 {
		return ie.trueInFactByZNot0(fact)
	}

	if fact.Params[1].String() == glob.KeywordQNot0 {
		return ie.trueInFactByQNot0(fact)
	}

	return glob.NewEmptyShortTrueRet()
}

// trueInFactByNamedFnSet handles inference for x $in fnTemplate(...)
// Inference: Derives a universal fact from the function template definition
// and stores the function-template satisfaction relationship
func (ie *InferEngine) trueInFactByNamedFnSet(fact *ast.SpecFactStmt) *glob.ShortRet {
	isTemplate, ret := ie.trueInFactInFnSet(fact)
	if ret.IsErr() {
		return ret
	}
	if isTemplate {
		return ret
	}
	return glob.NewEmptyShortUnknownRet()
}

// trueInFactByAnonymousFnSetObj handles inference for x $in fnTemplateFnObj
// Inference: Inserts the function x into the function template table
func (ie *InferEngine) trueInFactByAnonymousFnSetObj(fact *ast.SpecFactStmt) *glob.ShortRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsFnTemplate_ObjFn(fnFn) {
		return glob.NewEmptyShortUnknownRet()
	}

	fnTStruct, ok := ie.EnvMgr.AnonymousFnToInstFnTemplate(fnFn)
	if !ok {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("%s is not obj type fn template", fnFn.String())})
	}

	ret := ie.EnvMgr.InsertFnInFnTT(fact.Params[0], fnTStruct)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewEmptyShortTrueRet()
}

// trueInFactByCart handles inference for x $in cart(S1, S2, ..., Sn)
// It tries both direct cart and cart from equal facts
// Inference: If x is in a cartesian product, then each component of x is in the corresponding set
func (ie *InferEngine) trueInFactByCart(fact *ast.SpecFactStmt) *glob.ShortRet {
	// Try direct cart first
	if fnObj, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordCart) {
		return ie.trueInFactInCart(fact.Params[0], fnObj)
	}

	// Try cart from equal facts
	equalObjs, ok := ie.EnvMgr.GetEqualObjs(fact.Params[1])
	if !ok || equalObjs == nil {
		return glob.NewEmptyShortUnknownRet()
	}

	// Look for a cart set in the equal facts
	for _, equalObj := range *equalObjs {
		if cartAsFn, ok := equalObj.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
			return ie.trueInFactInCart(fact.Params[0], cartAsFn)
		}
	}

	return glob.NewEmptyShortUnknownRet()
}

// trueInFactInCart handles inference for obj $in cart(S1, S2, ..., Sn)
// Inference generates:
//   - a[i] $in Si for each i (each component is in the corresponding set)
//   - dim(a) = n (dimension equals the number of sets)
//   - is_tuple(a) (the object is a tuple)
func (ie *InferEngine) trueInFactInCart(obj ast.Obj, cartSet *ast.FnObj) *glob.ShortRet {
	derivedFacts := []string{}

	// 为每个索引生成 a[i] $in cartSet.Params[i-1] 的事实（索引从1开始）
	for i := range len(cartSet.Params) {
		index := i + 1 // 索引从1开始
		indexObj := ast.Atom(fmt.Sprintf("%d", index))
		// 创建索引操作 a[i]
		indexedObj := ast.NewFnObj(ast.Atom(glob.KeywordObjAtIndexOpt), []ast.Obj{obj, indexObj})
		// 创建 a[i] $in cartSet.Params[i] 的事实
		inFact := ast.NewInFactWithObj(indexedObj, cartSet.Params[i])
		ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inFact)
		if ret.IsErr() {
			return glob.ErrStmtMsgToShortRet(ret)
		}
		derivedFacts = append(derivedFacts, inFact.String())
	}
	// 添加 dim(obj) = len(cartSet.Params) 的事实
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj})
	dimValue := ast.Atom(strconv.Itoa(len(cartSet.Params)))
	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(dimEqualFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, dimEqualFact.String())
	// 添加 is_tuple(obj) 的事实
	isTupleFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.BuiltinLine0)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(isTupleFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, isTupleFact.String())
	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) trueInFactInFnSet(fact *ast.SpecFactStmt) (bool, *glob.ShortRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, glob.NewEmptyShortTrueRet()
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, glob.NewEmptyShortTrueRet()
	}

	def := ie.EnvMgr.GetFnTemplateDef_KeyIsObjHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, glob.NewEmptyShortTrueRet()
	}

	fnTNoName, ok, ret := ie.EnvMgr.getInstantiatedFnTTOfFnObj(fact.Params[1].(*ast.FnObj))
	if ret.IsErr() {
		return false, glob.NewShortRet(glob.StmtRetTypeError, ret.Error)
	}
	if !ok {
		return false, glob.NewEmptyShortTrueRet()
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, glob.NewShortRet(glob.StmtRetTypeError, []string{err.Error()})
	}

	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(derivedFact)
	if ret.IsErr() {
		return false, glob.NewShortRet(glob.StmtRetTypeError, ret.Error)
	}

	ret = ie.EnvMgr.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, glob.NewShortRet(glob.StmtRetTypeError, ret.Error)
	}

	return true, glob.NewEmptyShortTrueRet()
}

// trueInFactByListSet handles inference for x $in listSet(...)
// It tries to get the listSet either directly or from equal facts
// Inference: If x is in a finite list set, then x equals one of the elements
func (ie *InferEngine) trueInFactByListSet(fact *ast.SpecFactStmt) *glob.ShortRet {
	// Try to get listSet, either directly or from equal facts
	listSetObj := ie.EnvMgr.GetListSetEqualToObj(fact.Params[1])
	if listSetObj == nil {
		return glob.NewEmptyShortUnknownRet()
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("expected list set to be FnObj, got %T", listSetObj)})
	}

	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{}, glob.BuiltinLine0)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], param}, glob.BuiltinLine0))
	}
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(orFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{orFact.String()})
}

// trueInFactBySetBuilder handles inference for x $in {y in T: P(y)}
// Inference: If x is in a set builder, then x is in the parent set T and satisfies all intentional facts P(x)
func (ie *InferEngine) trueInFactBySetBuilder(fact *ast.SpecFactStmt) *glob.ShortRet {
	setBuilderObj := ie.EnvMgr.GetSetBuilderEqualToObj(fact.Params[1])
	if setBuilderObj == nil {
		return glob.NewEmptyShortUnknownRet()
	}

	return ie.trueInFactInSetBuilder(fact.Params[0], setBuilderObj)
}

// trueInFactInSetBuilder handles inference for obj $in {param in parentSet: facts}
// Inference generates:
//   - obj $in parentSet (membership in parent set)
//   - All instantiated intentional facts from the set builder
func (ie *InferEngine) trueInFactInSetBuilder(obj ast.Obj, setBuilderObj *ast.FnObj) *glob.ShortRet {
	derivedFactStrings := []string{}
	setBuilderStruct, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{err.Error()})
	}

	uniMap := map[string]ast.Obj{setBuilderStruct.Param: obj}

	instFacts := []ast.FactStmt{}

	for _, fact := range setBuilderStruct.Facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return glob.NewShortRet(glob.StmtRetTypeError, []string{err.Error()})
		}
		instFacts = append(instFacts, instFact)
	}

	// in parent set
	inParentSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeywordIn), []ast.Obj{obj, setBuilderStruct.ParentSet}, glob.BuiltinLine0)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inParentSetFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFactStrings = append(derivedFactStrings, inParentSetFact.String())

	// intentional facts are true
	for _, fact := range instFacts {
		ret := ie.EnvMgr.NewFactWithCheckingNameDefined(fact)
		if ret.IsErr() {
			return glob.ErrStmtMsgToShortRet(ret)
		}
		derivedFactStrings = append(derivedFactStrings, fact.String())
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFactStrings)
}

// trueInFactByRangeOrClosedRange handles inference for x $in range(a, b) or x $in closed_range(a, b)
// Inference generates:
//   - x $in Z (integer membership)
//   - x >= a (lower bound)
//   - x < b (for range) or x <= b (for closed_range)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, etc.)
func (ie *InferEngine) trueInFactByRangeOrClosedRange(fact *ast.SpecFactStmt) *glob.ShortRet {
	// Check if the second parameter is a range or closed_range function call
	if !ast.ObjIsRangeOrClosedRangeWith2Params(fact.Params[1]) {
		return glob.NewEmptyShortUnknownRet()
	}

	derivedFactStrings := []string{}

	obj := fact.Params[0]
	rangeOrClosedRange := fact.Params[1].(*ast.FnObj)
	left := rangeOrClosedRange.Params[0]
	right := rangeOrClosedRange.Params[1]
	isRange := rangeOrClosedRange.FnHead.String() == glob.KeywordRange

	// in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret := ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFactStrings = append(derivedFactStrings, inZFact.String())
	derivedFactStrings = append(derivedFactStrings, "\n")

	// Generate x >= left
	greaterEqualLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, left}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualLeftFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFactStrings = append(derivedFactStrings, greaterEqualLeftFact.String())
	var retShort *glob.ShortRet
	retShort = ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterEqualLeftFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFactStrings = append(derivedFactStrings, retShort.Msgs...)

	// Generate left <= x
	lessEqualLeftFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{left, obj}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(lessEqualLeftFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFactStrings = append(derivedFactStrings, lessEqualLeftFact.String())
	retShort = ie.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(lessEqualLeftFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFactStrings = append(derivedFactStrings, retShort.Msgs...)

	if isRange {
		// range: generate x < right
		lessRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessRightFact)
		if ret.IsErr() {
			return glob.ErrStmtMsgToShortRet(ret)
		}
		derivedFactStrings = append(derivedFactStrings, lessRightFact.String())
		retShort = ie.BuiltinPropExceptTrueEqual(lessRightFact)
		if retShort.IsErr() {
			return retShort
		}
		if retShort.IsUnknown() {
			return glob.NewShortRet(glob.StmtRetTypeUnknown, retShort.Msgs)
		}
		derivedFactStrings = append(derivedFactStrings, retShort.Msgs...)
	} else {
		// closed_range: generate x <= right
		lessEqualRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessEqualRightFact)
		if ret.IsErr() {
			return glob.ErrStmtMsgToShortRet(ret)
		}
		derivedFactStrings = append(derivedFactStrings, lessEqualRightFact.String())
		retShort = ie.BuiltinPropExceptTrueEqual(lessEqualRightFact)
		if retShort.IsErr() {
			return retShort
		}
		if retShort.IsUnknown() {
			return glob.NewShortRet(glob.StmtRetTypeUnknown, retShort.Msgs)
		}
		derivedFactStrings = append(derivedFactStrings, retShort.Msgs...)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFactStrings)
}

// trueInFactByN handles inference for x $in N (natural numbers including 0)
// Inference generates:
//   - 0 <= x (non-negativity fact)
// func (ie *InferEngine) trueInFactByN(fact *ast.SpecFactStmt) *glob.ShortRet {
// 	derivedFacts := []string{}

// 	obj := fact.Params[0]

// 	// 0 <= x
// 	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{ast.Atom("0"), obj}, glob.BuiltinLine0)
// 	ret := ie.EnvMgr.storeSpecFactInMem(greaterEqualZeroFact)
// 	if ret.IsErr() {
// 		return glob.ErrStmtMsgToShortRet(ret)
// 	}
// 	derivedFacts = append(derivedFacts, greaterEqualZeroFact.String())

// 	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
// }

// trueInFactByNPos handles inference for x $in NPos (positive natural numbers)
// Inference generates:
//   - x $in N, x $in Q, x $in R (number type memberships)
//   - x > 0, x >= 1 (positivity facts)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByNPos(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in N
	inNFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordNatural))
	ret := ie.EnvMgr.storeSpecFactInMem(inNFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inNFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	// x >= 1
	greaterEqualOneFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("1")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualOneFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterEqualOneFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByRPos handles inference for x $in RPos (positive real numbers)
// Inference generates:
//   - x $in R (real number membership)
//   - x > 0 (positivity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByRPos(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret := ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByRNeg handles inference for x $in RNeg (negative real numbers)
// Inference generates:
//   - x $in R (real number membership)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByRNeg(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret := ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByZNeg handles inference for x $in ZNeg (negative integers)
// Inference generates:
//   - x $in Z (integer membership)
//   - x $in Q, x $in R (number type memberships)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByZNeg(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret := ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inZFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByQNeg handles inference for x $in QNeg (negative rational numbers)
// Inference generates:
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByQNeg(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret := ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByQPos handles inference for x $in QPos (positive rational numbers)
// Inference generates:
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
//   - x > 0 (positivity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByQPos(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret := ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		return retShort
	}
	derivedFacts = append(derivedFacts, retShort.Msgs...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByRNot0 handles inference for x $in R_not0 (non-zero real numbers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in R (real number membership)
func (ie *InferEngine) trueInFactByRNot0(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notEqualZeroFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByZNot0 handles inference for x $in Z_not0 (non-zero integers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in Z (integer membership)
func (ie *InferEngine) trueInFactByZNot0(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notEqualZeroFact.String())

	// x $in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret = ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inZFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactByQNot0 handles inference for x $in Q_not0 (non-zero rational numbers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
func (ie *InferEngine) trueInFactByQNot0(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewSpecFactStmt(ast.FalsePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notEqualZeroFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inRFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactBySetOperations handles inference for set operations (cup, cap, union, intersect, power_set, set_minus)
// It checks if the second parameter is a set operation function call
func (ie *InferEngine) trueInFactBySetOperations(fact *ast.SpecFactStmt) *glob.ShortRet {
	fnObj, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return glob.NewEmptyShortUnknownRet()
	}

	head, ok := fnObj.IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return glob.NewEmptyShortUnknownRet()
	}

	headStr := string(head)

	// Try direct set operation first
	switch headStr {
	case glob.KeywordCup:
		return ie.trueInFactInCup(fact.Params[0], fnObj)
	case glob.KeywordCap:
		return ie.trueInFactInCap(fact.Params[0], fnObj)
	case glob.KeywordUnion:
		if len(fnObj.Params) == 2 {
			return ie.trueInFactInUnion(fact.Params[0], fnObj.Params[0], fnObj.Params[1])
		}
	case glob.KeywordIntersect:
		if len(fnObj.Params) == 2 {
			return ie.trueInFactInIntersect(fact.Params[0], fnObj.Params[0], fnObj.Params[1])
		}
	case glob.KeywordPowerSet:
		if len(fnObj.Params) == 1 {
			return ie.trueInFactInPowerSet(fact.Params[0], fnObj.Params[0])
		}
	case glob.KeywordSetMinus:
		if len(fnObj.Params) == 2 {
			return ie.trueInFactInSetMinus(fact.Params[0], fnObj.Params[0], fnObj.Params[1])
		}
	}

	return glob.NewEmptyShortUnknownRet()
}

// trueInFactInCup handles inference for item $in cup(x)
// Inference: exist x_item x st item $in x_item
func (ie *InferEngine) trueInFactInCup(item ast.Obj, cupSet *ast.FnObj) *glob.ShortRet {
	if len(cupSet.Params) != 1 {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("cup expects 1 parameter, got %d", len(cupSet.Params))})
	}

	x := cupSet.Params[0]
	xItemParam := ie.EnvMgr.GenerateUndeclaredRandomName()

	// Create exist fact: exist x_item x st item $in x_item
	existFact := ast.NewExistStFact(
		ast.TrueExist_St,
		ast.Atom(glob.KeywordIn),
		true,
		[]string{xItemParam},
		[]ast.Obj{x},
		[]ast.Obj{item, ast.Atom(xItemParam)},
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(existFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{existFact.String()})
}

// trueInFactInCap handles inference for item $in cap(x)
// Inference: forall x_item x: item $in x_item
func (ie *InferEngine) trueInFactInCap(item ast.Obj, capSet *ast.FnObj) *glob.ShortRet {
	if len(capSet.Params) != 1 {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("cap expects 1 parameter, got %d", len(capSet.Params))})
	}

	x := capSet.Params[0]
	xItemParam := ie.EnvMgr.GenerateUndeclaredRandomName()

	// Create forall fact: forall x_item x: item $in x_item
	inFact := ast.NewInFactWithParamObj(ast.Atom(xItemParam), x, glob.BuiltinLine0)
	thenFact := ast.NewInFactWithObj(item, ast.Atom(xItemParam))

	uniFact := ast.NewUniFact(
		[]string{xItemParam},
		[]ast.Obj{x},
		[]ast.FactStmt{inFact},
		[]ast.FactStmt{thenFact},
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{uniFact.String()})
}

// trueInFactInUnion handles inference for item $in union(x, y)
// Inference: item $in x or item $in y
func (ie *InferEngine) trueInFactInUnion(item ast.Obj, x ast.Obj, y ast.Obj) *glob.ShortRet {
	// Create or fact: item $in x or item $in y
	inXFact := ast.NewInFactWithObj(item, x)
	inYFact := ast.NewInFactWithObj(item, y)

	orFact := ast.NewOrStmt([]*ast.SpecFactStmt{inXFact, inYFact}, glob.BuiltinLine0)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(orFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{orFact.String()})
}

// trueInFactInIntersect handles inference for item $in intersect(x, y)
// Inference: item $in x and item $in y
func (ie *InferEngine) trueInFactInIntersect(item ast.Obj, x ast.Obj, y ast.Obj) *glob.ShortRet {
	derivedFacts := []string{}

	// Create fact: item $in x
	inXFact := ast.NewInFactWithObj(item, x)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inXFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inXFact.String())

	// Create fact: item $in y
	inYFact := ast.NewInFactWithObj(item, y)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(inYFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inYFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

// trueInFactInPowerSet handles inference for y $in power_set(x)
// Inference: y $subset_of x
func (ie *InferEngine) trueInFactInPowerSet(y ast.Obj, x ast.Obj) *glob.ShortRet {
	// Create fact: y $subset_of x
	subsetFact := ast.NewSpecFactStmt(
		ast.TruePure,
		ast.Atom(glob.KeywordSubsetOf),
		[]ast.Obj{y, x},
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(subsetFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{subsetFact.String()})
}

// trueInFactInSetMinus handles inference for item $in set_minus(x, y)
// Inference: item $in x and not item $in y
func (ie *InferEngine) trueInFactInSetMinus(item ast.Obj, x ast.Obj, y ast.Obj) *glob.ShortRet {
	derivedFacts := []string{}

	// Create fact: item $in x
	inXFact := ast.NewInFactWithObj(item, x)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inXFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, inXFact.String())

	// Create fact: not item $in y
	notInYFact := ast.NewSpecFactStmt(
		ast.FalsePure,
		ast.Atom(glob.KeywordIn),
		[]ast.Obj{item, y},
		glob.BuiltinLine0,
	)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(notInYFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notInYFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}

func (ie *InferEngine) trueInFactByN(fact *ast.SpecFactStmt) *glob.ShortRet {
	derivedFacts := []string{}

	obj := fact.Params[0]

	// 0 <= x
	lessEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{ast.Atom("0"), obj}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	// x >= 0
	greaterEqualZeroFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, greaterEqualZeroFact.String())

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}
