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

func (ie *InferEngine) trueInFact(fact ast.SpecificFactStmt) ast.StmtRet {
	asFact, ok := fact.(*ast.PureSpecificFactStmt)
	if !ok || len(asFact.Params) != 2 {
		return ast.NewErrStmtEmptyRet(fact).AddExtraInfo(fmt.Sprintf("in fact expect 2 parameters, get %d in %s", len(asFact.Params), fact))
	}

	if ret := ie.trueInFactByNamedFnSet(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByAnonymousFnSetObj(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByCart(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByListSet(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactBySetBuilder(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactByRangeOrClosedRange(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if ret := ie.trueInFactBySetOperations(asFact); ret.IsTrue() || ret.IsErr() {
		return ret
	}

	if asFact.Params[1].String() == glob.KeywordNatural {
		return ie.trueInFactByN(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordNPos {
		return ie.trueInFactByNPos(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordRPos {
		return ie.trueInFactByRPos(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordRNeg {
		return ie.trueInFactByRNeg(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordZNeg {
		return ie.trueInFactByZNeg(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordQNeg {
		return ie.trueInFactByQNeg(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordQPos {
		return ie.trueInFactByQPos(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordRNot0 {
		return ie.trueInFactByRNot0(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordZNot0 {
		return ie.trueInFactByZNot0(asFact)
	}

	if asFact.Params[1].String() == glob.KeywordQNot0 {
		return ie.trueInFactByQNot0(asFact)
	}

	return ast.NewTrueStmtEmptyRet(asFact)
}

// trueInFactByNamedFnSet handles inference for x $in fnTemplate(...)
// Inference: Derives a universal fact from the function template definition
// and stores the function-template satisfaction relationship
func (ie *InferEngine) trueInFactByNamedFnSet(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	isTemplate, ret := ie.trueInFactInFnSet(fact)
	if ret.IsErr() {
		return ast.NewErrStmtEmptyRet(fact)
	}
	if isTemplate {
		return ast.NewTrueStmtEmptyRet(fact)
	}
	return ast.NewUnknownStmtEmptyRet(fact)
}

// trueInFactByAnonymousFnSetObj handles inference for x $in fnTemplateFnObj
// Inference: Inserts the function x into the function template table
func (ie *InferEngine) trueInFactByAnonymousFnSetObj(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	fnFn, ok := fact.Params[1].(*ast.FnObj)
	if !ok || !ast.IsAnonymousFnSet(fnFn) {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	fnTStruct, ok := ie.EnvMgr.AnonymousFnToInstFnTemplate(fnFn)
	if !ok {
		return ast.NewErrStmtEmptyRet(fact).AddExtraInfo(fmt.Sprintf("%s is not obj type fn template", fnFn.String()))
	}

	ok = ie.EnvMgr.InsertFnInFnTT(fact.Params[0], fnTStruct)
	if !ok {
		return ast.NewErrStmtEmptyRet(fact).AddExtraInfo("failed to insert function in function template table")
	}

	return ast.NewTrueStmtEmptyRet(fact)
}

// trueInFactByCart handles inference for x $in cart(S1, S2, ..., Sn)
// It tries both direct cart and cart from equal facts
// Inference: If x is in a cartesian product, then each component of x is in the corresponding set
func (ie *InferEngine) trueInFactByCart(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	// Try direct cart first
	if fnObj, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeywordCart) {
		return ie.trueInFactInCart(fact.Params[0], fnObj)
	}

	// Try cart from equal facts
	equalObjs, ok := ie.EnvMgr.GetEqualObjs(fact.Params[1])
	if !ok || equalObjs == nil {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	// Look for a cart set in the equal facts
	for _, equalObj := range *equalObjs {
		if cartAsFn, ok := equalObj.(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartAsFn.FnHead, glob.KeywordCart) {
			return ie.trueInFactInCart(fact.Params[0], cartAsFn)
		}
	}

	return ast.NewUnknownStmtEmptyRet(fact)
}

// trueInFactInCart handles inference for obj $in cart(S1, S2, ..., Sn)
// Inference generates:
//   - a[i] $in Si for each i (each component is in the corresponding set)
//   - dim(a) = n (dimension equals the number of sets)
//   - is_tuple(a) (the object is a tuple)
func (ie *InferEngine) trueInFactInCart(obj ast.Obj, cartSet *ast.FnObj) ast.StmtRet {
	// 创建一个临时 fact 用于返回
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{obj, ast.NewFnObj(ast.Atom(glob.KeywordCart), cartSet.Params)}, glob.BuiltinLine0)
	result := ast.NewTrueStmtEmptyRet(tempFact)

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
			return ret
		}
		result.AddExtraInfo(inFact.String())
	}
	// 添加 dim(obj) = len(cartSet.Params) 的事实
	dimFn := ast.NewFnObj(ast.Atom(glob.KeywordDim), []ast.Obj{obj})
	dimValue := ast.Atom(strconv.Itoa(len(cartSet.Params)))
	dimEqualFact := ast.NewEqualFact(dimFn, dimValue)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(dimEqualFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(dimEqualFact.String())
	// 添加 is_tuple(obj) 的事实
	isTupleFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIsTuple), []ast.Obj{obj}, glob.BuiltinLine0)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(isTupleFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(isTupleFact.String())
	return result
}

func (ie *InferEngine) trueInFactInFnSet(fact *ast.PureSpecificFactStmt) (bool, ast.StmtRet) {
	if _, ok := fact.Params[1].(*ast.FnObj); !ok {
		return false, ast.NewTrueStmtEmptyRet(fact)
	}

	head, ok := fact.Params[1].(*ast.FnObj).IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return false, ast.NewTrueStmtEmptyRet(fact)
	}

	def := ie.EnvMgr.GetFnTemplateDef_KeyIsObjHead(fact.Params[1].(*ast.FnObj))
	if def == nil {
		return false, ast.NewTrueStmtEmptyRet(fact)
	}

	fnTNoName, ok, err := ie.EnvMgr.getInstantiatedFnTTOfFnObj(fact.Params[1].(*ast.FnObj))
	if err != nil {
		return false, ast.NewErrStmtEmptyRet(fact).AddExtraInfo(err.Error())
	}
	if !ok {
		return false, ast.NewTrueStmtEmptyRet(fact)
	}

	templateParamUniMap := map[string]ast.Obj{}
	for i, param := range def.TemplateDefHeader.Params {
		templateParamUniMap[param] = fact.Params[1].(*ast.FnObj).Params[i]
	}

	derivedFact, err := fnTNoName.DeriveUniFact(string(head), fact.Params[0], templateParamUniMap)
	if err != nil {
		return false, ast.NewErrStmtEmptyRet(fact).AddExtraInfo(err.Error())
	}

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(derivedFact)
	if ret.IsErr() {
		return false, ret
	}

	ret = ie.EnvMgr.StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fact.Params[0], fact.Params[1].(*ast.FnObj), fnTNoName)
	if ret.IsErr() {
		return false, ret
	}

	return true, ast.NewTrueStmtEmptyRet(fact)
}

// trueInFactByListSet handles inference for x $in listSet(...)
// It tries to get the listSet either directly or from equal facts
// Inference: If x is in a finite list set, then x equals one of the elements
func (ie *InferEngine) trueInFactByListSet(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	// Try to get listSet, either directly or from equal facts
	listSetObj := ie.EnvMgr.GetListSetEqualToObj(fact.Params[1])
	if listSetObj == nil {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	listSetFnObj, ok := listSetObj.(*ast.FnObj)
	if !ok {
		return ast.NewErrStmtEmptyRet(fact).AddExtraInfo(fmt.Sprintf("expected list set to be FnObj, got %T", listSetObj))
	}

	orFact := ast.NewOrStmt([]ast.SpecificFactStmt{}, glob.BuiltinLine0)
	for _, param := range listSetFnObj.Params {
		orFact.Facts = append(orFact.Facts, ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], param}, glob.BuiltinLine0))
	}
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(orFact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueStmtEmptyRet(fact).AddExtraInfo(orFact.String())
}

// trueInFactBySetBuilder handles inference for x $in {y in T: P(y)}
// Inference: If x is in a set builder, then x is in the parent set T and satisfies all intentional facts P(x)
func (ie *InferEngine) trueInFactBySetBuilder(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	setBuilderObj := ie.EnvMgr.GetSetBuilderEqualToObj(fact.Params[1])
	if setBuilderObj == nil {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	return ie.trueInFactInSetBuilder(fact.Params[0], setBuilderObj)
}

// trueInFactInSetBuilder handles inference for obj $in {param in parentSet: facts}
// Inference generates:
//   - obj $in parentSet (membership in parent set)
//   - All instantiated intentional facts from the set builder
func (ie *InferEngine) trueInFactInSetBuilder(obj ast.Obj, setBuilderObj *ast.FnObj) ast.StmtRet {
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{obj, setBuilderObj}, glob.BuiltinLine0)
	result := ast.NewTrueStmtEmptyRet(tempFact)
	
	setBuilderStruct, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return ast.NewErrStmtEmptyRet(tempFact).AddExtraInfo(err.Error())
	}

	uniMap := map[string]ast.Obj{setBuilderStruct.Param: obj}

	instFacts := []ast.FactStmt{}

	for _, fact := range setBuilderStruct.Facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return ast.NewErrStmtEmptyRet(tempFact).AddExtraInfo(err.Error())
		}
		instFacts = append(instFacts, instFact)
	}

	// in parent set
	inParentSetFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{obj, setBuilderStruct.ParentSet}, glob.BuiltinLine0)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inParentSetFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inParentSetFact.String())

	// intentional facts are true
	for _, fact := range instFacts {
		ret := ie.EnvMgr.NewFactWithCheckingNameDefined(fact)
		if ret.IsErr() {
			return ret
		}
		result.AddExtraInfo(fact.String())
	}

	return result
}

// trueInFactByRangeOrClosedRange handles inference for x $in range(a, b) or x $in closed_range(a, b)
// Inference generates:
//   - x $in Z (integer membership)
//   - x >= a (lower bound)
//   - x < b (for range) or x <= b (for closed_range)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, etc.)
func (ie *InferEngine) trueInFactByRangeOrClosedRange(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	// Check if the second parameter is a range or closed_range function call
	if !ast.ObjIsRangeOrClosedRangeWith2Params(fact.Params[1]) {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	result := ast.NewTrueStmtEmptyRet(fact)

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
	result.AddExtraInfo(inZFact.String())
	result.AddExtraInfo("\n")

	// Generate x >= left
	greaterEqualLeftFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, left}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterEqualLeftFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterEqualLeftFact)
	if retShort.IsErr() {
		// Convert ShortRet to StmtRet
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	// Generate left <= x
	lessEqualLeftFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{left, obj}, fact.Line)
	ret = ie.EnvMgr.storeSpecFactInMem(lessEqualLeftFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(lessEqualLeftFact.String())
	retShort = ie.builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero(lessEqualLeftFact)
	if retShort.IsErr() {
		// Convert ShortRet to StmtRet
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	if isRange {
		// range: generate x < right
		lessRightFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessRightFact)
		if ret.IsErr() {
			return ret
		}
		result.AddExtraInfo(lessRightFact.String())
		retStmt := ie.BuiltinPropExceptTrueEqual(lessRightFact)
		if retStmt.IsErr() {
			return retStmt
		}
		if retStmt.IsUnknown() {
			if unknownRet, ok := retStmt.(*ast.UnknownStmtRet); ok {
				unknownResult := ast.NewUnknownStmtEmptyRet(fact)
				for _, info := range unknownRet.ExtraInfo {
					unknownResult.AddExtraInfo(info)
				}
				return unknownResult
			}
			return ast.NewUnknownStmtEmptyRet(fact)
		}
		if trueRet, ok := retStmt.(*ast.TrueStmtRet); ok {
			result.AddExtraInfos(trueRet.ExtraInfo)
		}
	} else {
		// closed_range: generate x <= right
		lessEqualRightFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{obj, right}, fact.Line)
		ret = ie.EnvMgr.storeSpecFactInMem(lessEqualRightFact)
		if ret.IsErr() {
			return ret
		}
		result.AddExtraInfo(lessEqualRightFact.String())
		retStmt := ie.BuiltinPropExceptTrueEqual(lessEqualRightFact)
		if retStmt.IsErr() {
			return retStmt
		}
		if retStmt.IsUnknown() {
			if unknownRet, ok := retStmt.(*ast.UnknownStmtRet); ok {
				unknownResult := ast.NewUnknownStmtEmptyRet(fact)
				for _, info := range unknownRet.ExtraInfo {
					unknownResult.AddExtraInfo(info)
				}
				return unknownResult
			}
			return ast.NewUnknownStmtEmptyRet(fact)
		}
		if trueRet, ok := retStmt.(*ast.TrueStmtRet); ok {
			result.AddExtraInfos(trueRet.ExtraInfo)
		}
	}

	return result
}

// trueInFactByN handles inference for x $in N (natural numbers including 0)
// Inference generates:
//   - 0 <= x (non-negativity fact)
// func (ie *InferEngine) trueInFactByN(fact *ast.SpecFactStmt) ast.ShortRet {
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
func (ie *InferEngine) trueInFactByNPos(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in N
	inNFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordNatural))
	ret := ie.EnvMgr.storeSpecFactInMem(inNFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inNFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	// x >= 1
	greaterEqualOneFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("1")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualOneFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterEqualOneFact.String())

	return result
}

// trueInFactByRPos handles inference for x $in RPos (positive real numbers)
// Inference generates:
//   - x $in R (real number membership)
//   - x > 0 (positivity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByRPos(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret := ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	return result
}

// trueInFactByRNeg handles inference for x $in RNeg (negative real numbers)
// Inference generates:
//   - x $in R (real number membership)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByRNeg(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret := ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	return result
}

// trueInFactByZNeg handles inference for x $in ZNeg (negative integers)
// Inference generates:
//   - x $in Z (integer membership)
//   - x $in Q, x $in R (number type memberships)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByZNeg(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret := ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inZFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	return result
}

// trueInFactByQNeg handles inference for x $in QNeg (negative rational numbers)
// Inference generates:
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
//   - x < 0 (negativity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, -x > 0, etc.)
func (ie *InferEngine) trueInFactByQNeg(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret := ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x < 0
	lessThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLess), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(lessThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(lessThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero(lessThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	return result
}

// trueInFactByQPos handles inference for x $in QPos (positive rational numbers)
// Inference generates:
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
//   - x > 0 (positivity fact)
//   - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)
func (ie *InferEngine) trueInFactByQPos(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret := ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	// x > 0
	greaterThanZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolGreater), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterThanZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterThanZeroFact.String())
	retShort := ie.builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero(greaterThanZeroFact)
	if retShort.IsErr() {
		if errRet, ok := retShort.(*ast.ErrShortRet); ok {
			errResult := ast.NewErrStmtEmptyRet(fact)
			for _, msg := range errRet.Msg {
				errResult.AddExtraInfo(msg)
			}
			return errResult
		}
		return ast.NewErrStmtEmptyRet(fact)
	}
	if trueRet, ok := retShort.(*ast.TrueShortRet); ok {
		result.AddExtraInfos(trueRet.Msg)
	}

	return result
}

// trueInFactByRNot0 handles inference for x $in R_not0 (non-zero real numbers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in R (real number membership)
func (ie *InferEngine) trueInFactByRNot0(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(notEqualZeroFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	return result
}

// trueInFactByZNot0 handles inference for x $in Z_not0 (non-zero integers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in Z (integer membership)
func (ie *InferEngine) trueInFactByZNot0(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(notEqualZeroFact.String())

	// x $in Z
	inZFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordInteger))
	ret = ie.EnvMgr.storeSpecFactInMem(inZFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inZFact.String())

	return result
}

// trueInFactByQNot0 handles inference for x $in Q_not0 (non-zero rational numbers)
// Inference generates:
//   - x != 0 (non-zero fact)
//   - x $in Q (rational number membership)
//   - x $in R (real number membership)
func (ie *InferEngine) trueInFactByQNot0(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// x != 0
	notEqualZeroFact := ast.NewPureSpecificFactStmt(false, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(notEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(notEqualZeroFact.String())

	// x $in Q
	inQFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordRational))
	ret = ie.EnvMgr.storeSpecFactInMem(inQFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inQFact.String())

	// x $in R
	inRFact := ast.NewInFactWithObj(obj, ast.Atom(glob.KeywordReal))
	ret = ie.EnvMgr.storeSpecFactInMem(inRFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inRFact.String())

	return result
}

// trueInFactBySetOperations handles inference for set operations (cup, cap, union, intersect, power_set, set_minus)
// It checks if the second parameter is a set operation function call
func (ie *InferEngine) trueInFactBySetOperations(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	fnObj, ok := fact.Params[1].(*ast.FnObj)
	if !ok {
		return ast.NewUnknownStmtEmptyRet(fact)
	}

	head, ok := fnObj.IsObjFn_HasAtomHead_ReturnHead()
	if !ok {
		return ast.NewUnknownStmtEmptyRet(fact)
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

	return ast.NewUnknownStmtEmptyRet(fact)
}

// trueInFactInCup handles inference for item $in cup(x)
// Inference: exist x_item x st item $in x_item
func (ie *InferEngine) trueInFactInCup(item ast.Obj, cupSet *ast.FnObj) ast.StmtRet {
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, cupSet}, glob.BuiltinLine0)
	
	if len(cupSet.Params) != 1 {
		return ast.NewErrStmtEmptyRet(tempFact).AddExtraInfo(fmt.Sprintf("cup expects 1 parameter, got %d", len(cupSet.Params)))
	}

	xItemParam := ie.EnvMgr.GenerateUnusedRandomName()

	// Create exist fact: exist x_item x st item $in x_item
	pureFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, ast.Atom(xItemParam)}, glob.BuiltinLine0)
	existFact := ast.NewExistSpecificFactStmt(
		true,
		[]string{xItemParam},
		[]ast.Obj{cupSet.Params[0]},
		pureFact,
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(existFact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueStmtEmptyRet(tempFact).AddExtraInfo(existFact.String())
}

// trueInFactInCap handles inference for item $in cap(x)
// Inference: forall x_item x: item $in x_item
func (ie *InferEngine) trueInFactInCap(item ast.Obj, capSet *ast.FnObj) ast.StmtRet {
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, capSet}, glob.BuiltinLine0)
	
	if len(capSet.Params) != 1 {
		return ast.NewErrStmtEmptyRet(tempFact).AddExtraInfo(fmt.Sprintf("cap expects 1 parameter, got %d", len(capSet.Params)))
	}

	x := capSet.Params[0]
	xItemParam := ie.EnvMgr.GenerateUnusedRandomName()

	// Create forall fact: forall x_item x: item $in x_item
	inFact := ast.NewInFactWithParamObj(ast.Atom(xItemParam), x, glob.BuiltinLine0)
	thenFact := ast.NewInFactWithObj(item, ast.Atom(xItemParam))

	uniFact := ast.NewUniFact(
		[]string{xItemParam},
		[]ast.Obj{x},
		[]ast.Spec_OrFact{inFact},
		[]ast.Spec_OrFact{thenFact},
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(uniFact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueStmtEmptyRet(tempFact).AddExtraInfo(uniFact.String())
}

// trueInFactInUnion handles inference for item $in union(x, y)
// Inference: item $in x or item $in y
func (ie *InferEngine) trueInFactInUnion(item ast.Obj, x ast.Obj, y ast.Obj) ast.StmtRet {
	unionSet := ast.NewFnObj(ast.Atom(glob.KeywordUnion), []ast.Obj{x, y})
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, unionSet}, glob.BuiltinLine0)
	
	// Create or fact: item $in x or item $in y
	inXFact := ast.NewInFactWithObj(item, x)
	inYFact := ast.NewInFactWithObj(item, y)

	orFact := ast.NewOrStmt([]ast.SpecificFactStmt{inXFact, inYFact}, glob.BuiltinLine0)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(orFact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueStmtEmptyRet(tempFact).AddExtraInfo(orFact.String())
}

// trueInFactInIntersect handles inference for item $in intersect(x, y)
// Inference: item $in x and item $in y
func (ie *InferEngine) trueInFactInIntersect(item ast.Obj, x ast.Obj, y ast.Obj) ast.StmtRet {
	intersectSet := ast.NewFnObj(ast.Atom(glob.KeywordIntersect), []ast.Obj{x, y})
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, intersectSet}, glob.BuiltinLine0)
	result := ast.NewTrueStmtEmptyRet(tempFact)

	// Create fact: item $in x
	inXFact := ast.NewInFactWithObj(item, x)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inXFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inXFact.String())

	// Create fact: item $in y
	inYFact := ast.NewInFactWithObj(item, y)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(inYFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inYFact.String())

	return result
}

// trueInFactInPowerSet handles inference for y $in power_set(x)
// Inference: y $subset_of x
func (ie *InferEngine) trueInFactInPowerSet(y ast.Obj, x ast.Obj) ast.StmtRet {
	powerSet := ast.NewFnObj(ast.Atom(glob.KeywordPowerSet), []ast.Obj{x})
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{y, powerSet}, glob.BuiltinLine0)
	
	// Create fact: y $subset_of x
	subsetFact := ast.NewPureSpecificFactStmt(
		true,
		ast.Atom(glob.KeywordSubsetOf),
		[]ast.Obj{y, x},
		glob.BuiltinLine0,
	)

	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(subsetFact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueStmtEmptyRet(tempFact).AddExtraInfo(subsetFact.String())
}

// trueInFactInSetMinus handles inference for item $in set_minus(x, y)
// Inference: item $in x and not item $in y
func (ie *InferEngine) trueInFactInSetMinus(item ast.Obj, x ast.Obj, y ast.Obj) ast.StmtRet {
	setMinus := ast.NewFnObj(ast.Atom(glob.KeywordSetMinus), []ast.Obj{x, y})
	tempFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeywordIn), []ast.Obj{item, setMinus}, glob.BuiltinLine0)
	result := ast.NewTrueStmtEmptyRet(tempFact)

	// Create fact: item $in x
	inXFact := ast.NewInFactWithObj(item, x)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(inXFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(inXFact.String())

	// Create fact: not item $in y
	notInYFact := ast.NewPureSpecificFactStmt(
		false,
		ast.Atom(glob.KeywordIn),
		[]ast.Obj{item, y},
		glob.BuiltinLine0,
	)
	ret = ie.EnvMgr.NewFactWithCheckingNameDefined(notInYFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(notInYFact.String())

	return result
}

func (ie *InferEngine) trueInFactByN(fact *ast.PureSpecificFactStmt) ast.StmtRet {
	result := ast.NewTrueStmtEmptyRet(fact)

	obj := fact.Params[0]

	// 0 <= x
	lessEqualZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{ast.Atom("0"), obj}, glob.BuiltinLine0)
	ret := ie.EnvMgr.storeSpecFactInMem(lessEqualZeroFact)
	if ret.IsErr() {
		return ret
	}

	// x >= 0
	greaterEqualZeroFact := ast.NewPureSpecificFactStmt(true, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{obj, ast.Atom("0")}, glob.BuiltinLine0)
	ret = ie.EnvMgr.storeSpecFactInMem(greaterEqualZeroFact)
	if ret.IsErr() {
		return ret
	}
	result.AddExtraInfo(greaterEqualZeroFact.String())

	return result
}
