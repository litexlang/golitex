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

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"strconv"
)

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName))
}

func (stmt *UniFactWithIffStmt) NewUniFactWithThenToIff() *UniFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.IffFacts, stmt.UniFact.Line)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.UniFact.ThenFacts...)
	return newUniFact
}

func (stmt *UniFactWithIffStmt) NewUniFactWithIffToThen() *UniFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.UniFact.ThenFacts, stmt.UniFact.Line)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.IffFacts...)
	return newUniFact
}

func MergeOuterInnerUniFacts(outer *UniFactStmt, inner *UniFactStmt) *UniFactStmt {
	newOuter := NewUniFact(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, outer.Line)

	newOuter.Params = append(newOuter.Params, inner.Params...)
	newOuter.ParamSets = append(newOuter.ParamSets, inner.ParamSets...)
	newOuter.DomFacts = append(newOuter.DomFacts, inner.DomFacts...)

	if len(newOuter.Params) != len(newOuter.ParamSets) {
		return nil
	}

	return newOuter
}

func (defStmt *DefPropStmt) Make_PropToIff_IffToProp() (*UniFactStmt, *UniFactStmt, error) {
	propSpecFactParams := []Obj{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, Atom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, Atom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, propToIffDomFacts, defStmt.IffFacts, defStmt.Line)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact}, defStmt.Line)

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Obj{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, Atom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, Atom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact}, defStmt.Line)

	return IffToProp
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Obj{}
	for _, param := range defStmt.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, Atom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, Atom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	return propSpecFact
}

func (defStmt *DefExistPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Obj{}
	for _, param := range defStmt.DefBody.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, Atom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, Atom(defStmt.DefBody.DefHeader.Name), propSpecFactParams, defStmt.Line)

	return propSpecFact
}

func (stmt *SpecFactStmt) ReverseParameterOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Obj{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *SpecFactStmt) IsValidEqualFact() (bool, error) {
	if stmt.NameIs(glob.KeySymbolEqual) {
		if len(stmt.Params) == 2 {
			return true, nil
		} else {
			return false, fmt.Errorf("equal fact %s should have 2 params, but got %d", stmt, len(stmt.Params))
		}
	} else {
		return false, nil
	}
}

func (stmt *SpecFactStmt) IsBuiltinProp_ExceptEqual() bool {
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName)) && !stmt.NameIs(glob.KeySymbolEqual)
}

// func (stmt *SpecFactStmt) IsMathInductionFact() bool {
// 	return string(stmt.PropName) == glob.KeywordProveByMathInduction
// }

func NewInFact(param string, paramSet Obj) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIn), []Obj{Atom(param), paramSet}, glob.BuiltinLine)
}

func NewInFactWithParamFc(param Obj, paramSet Obj) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIn), []Obj{param, paramSet}, glob.BuiltinLine)
}

func NewInFactWithFc(param Obj, paramSet Obj) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIn), []Obj{param, paramSet}, glob.BuiltinLine)
}

func IsFnSet(fc Obj) bool {
	fcAsFcFn, ok := fc.(*FnObj)
	if !ok {
		return false
	}

	fcHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FnObj)
	if !ok {
		return false
	}

	return IsAtomObjAndEqualToStr(fcHeadAsFcFn.FnHead, glob.KeywordFn)
}

func (stmt *SpecFactStmt) ReverseSpecFactParamsOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("ReverseSpecFactParamsOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Obj{stmt.Params[1], stmt.Params[0]}
	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *DefLetStmt) NewInFacts() []*SpecFactStmt {
	facts := []*SpecFactStmt{}

	if len(stmt.Objs) != len(stmt.ObjSets) {
		panic("NewInFacts: len(stmt.Objs) != len(stmt.ObjSets)")
	}

	for i, obj := range stmt.Objs {
		paramSet := stmt.ObjSets[i]
		facts = append(facts, NewInFact(obj, paramSet))
	}

	return facts
}

func (defHeader *DefHeader) NewInFacts() []*SpecFactStmt {
	facts := []*SpecFactStmt{}
	for i, param := range defHeader.Params {
		facts = append(facts, NewInFact(param, defHeader.ParamSets[i]))
	}

	return facts
}

func Get_FnTemplate_InFcForm_ParamSetsAndRetSet(fc Obj) ([]Obj, Obj, bool) {
	// given fc must be a function
	fcAsFcFn, ok := fc.(*FnObj)
	if !ok {
		return nil, nil, false
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FnObj)
	if !ok {
		return nil, nil, false
	}

	if len(fcAsFcFn.Params) != 1 {
		return nil, nil, false
	}

	if !IsAtomObjAndEqualToStr(fcAsFcFnHeadAsFcFn.FnHead, glob.KeywordFn) {
		return nil, nil, false
	}

	paramSets := []Obj{}
	paramSets = append(paramSets, fcAsFcFnHeadAsFcFn.Params...)

	return paramSets, fcAsFcFn.Params[0], true
}

func MakeExistFactParamsSlice(existParams []Obj, paramsInFact []Obj) []Obj {
	lengthOfExistParams := len(existParams)

	factParams := []Obj{}
	factParams = append(factParams, Atom(fmt.Sprintf("%d", lengthOfExistParams)))
	factParams = append(factParams, existParams...)
	factParams = append(factParams, paramsInFact...)

	return factParams
}

func GetExistFactExistParamsAndFactParams(stmt *SpecFactStmt) ([]Obj, []Obj) {
	lengthOfExistParams, _ := strconv.Atoi(string(stmt.Params[0].(Atom)))

	existParams := []Obj{}
	factParams := []Obj{}
	for i := 1; i < lengthOfExistParams+1; i++ {
		existParams = append(existParams, stmt.Params[i])
	}

	for i := lengthOfExistParams + 1; i < len(stmt.Params); i++ {
		factParams = append(factParams, stmt.Params[i])
	}

	return existParams, factParams
}

func (factStmtSlice FactStmtSlice) InstantiateFact(uniMap map[string]Obj) (FactStmtSlice, error) {
	instantiatedFacts := FactStmtSlice{}
	for _, fact := range factStmtSlice {
		instantiatedFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedFacts = append(instantiatedFacts, instantiatedFact)
	}
	return instantiatedFacts, nil
}

func isFcWithFcFnHeadWithName(fc Obj, name string) bool {
	fcAsFcFn, ok := fc.(*FnObj)
	if !ok {
		return false
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FnObj)
	if !ok {
		return false
	}

	return IsAtomObjAndEqualToStr(fcAsFcFnHeadAsFcFn.FnHead, name)
}

func IsFnTemplate_FcFn(fcFn *FnObj) bool {
	return isFcWithFcFnHeadWithName(fcFn, glob.KeywordFn)
}

func IsFcAtomEqualToGivenString(fc Obj, name string) bool {
	fcAtom, ok := fc.(Atom)
	if !ok {
		return false
	}

	return string(fcAtom) == name
}

func TransformEnumToUniFact(setName Obj, enumFcs []Obj) (*UniFactStmt, []*SpecFactStmt, []*SpecFactStmt) {
	freeObjName := Atom(glob.RandomString(4))
	equalFactsInOrFact := []*SpecFactStmt{}
	itemsInSetFacts := []*SpecFactStmt{}
	for _, fc := range enumFcs {
		equalFactsInOrFact = append(equalFactsInOrFact, NewSpecFactStmt(TruePure, Atom(glob.KeySymbolEqual), []Obj{freeObjName, fc}, glob.BuiltinLine))
		itemsInSetFacts = append(itemsInSetFacts, NewSpecFactStmt(TruePure, Atom(glob.KeywordIn), []Obj{fc, setName}, glob.BuiltinLine))
	}

	pairwiseNotEqualFacts := []*SpecFactStmt{}
	for i := range len(enumFcs) {
		for j := range len(enumFcs) {
			if i == j {
				continue
			}
			pairwiseNotEqualFacts = append(pairwiseNotEqualFacts, NewSpecFactStmt(FalsePure, Atom(glob.KeySymbolEqual), []Obj{enumFcs[i], enumFcs[j]}, glob.BuiltinLine))
		}
	}

	orFact := NewOrStmt(equalFactsInOrFact, glob.BuiltinLine)
	forallItemInSetEqualToOneOfGivenItems := NewUniFact([]string{string(freeObjName)}, []Obj{setName}, []FactStmt{}, []FactStmt{orFact}, glob.BuiltinLine)

	return forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts
}

// func (stmt *IntensionalSetStmt) ToEquivalentUniFacts() (*UniFactStmt, *UniFactStmt, error) {
// 	leftDomFacts := []FactStmt{}
// 	for _, proof := range stmt.Facts {
// 		leftDomFacts = append(leftDomFacts, proof)
// 	}

// 	leftUniFact := NewUniFact([]string{stmt.Param}, []Obj{stmt.ParentSet}, leftDomFacts, []FactStmt{NewInFact(stmt.Param, stmt.CurSet)}, glob.BuiltinLine)

// 	rightThenFacts := []FactStmt{NewInFact(stmt.Param, stmt.ParentSet)}
// 	for _, proof := range stmt.Facts {
// 		rightThenFacts = append(rightThenFacts, proof)
// 	}

// 	rightUniFact := NewUniFact([]string{stmt.Param}, []Obj{stmt.CurSet}, []FactStmt{}, rightThenFacts, glob.BuiltinLine)

// 	return leftUniFact, rightUniFact, nil
// }

// func (stmt *HaveSetFnStmt) ToDefFnStmt() *DefFnStmt {
// 	return NewDefFnStmt(string(stmt.DefHeader.Name), NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, Atom(glob.KeywordSet), []FactStmt{}, []FactStmt{stmt.ToIntensionalSetStmt()}, stmt.Line), stmt.Line)
// }

// func (stmt *HaveSetFnStmt) ToIntensionalSetStmt() *IntensionalSetStmt {
// 	params := []Obj{}
// 	for _, param := range stmt.DefHeader.Params {
// 		params = append(params, Atom(param))
// 	}

// 	fnName := Atom(stmt.DefHeader.Name)
// 	curSet := NewFnObj(fnName, params)
// 	intensionalSetStmt := NewIntensionalSetStmt(curSet, stmt.Param, stmt.ParentSet, stmt.Proofs, stmt.Line)

// 	return intensionalSetStmt
// }

func (stmt *ProveInRangeSetStmt) UniFact() *UniFactStmt {
	return NewUniFact([]string{stmt.Param}, []Obj{stmt.IntensionalSet}, []FactStmt{}, stmt.ThenFacts, stmt.Line)
}

func (stmt *ProveInRangeStmt) UniFact() *UniFactStmt {
	params := []string{stmt.param}
	paramSets := []Obj{Atom(glob.KeywordInteger)}

	// Build dom facts: start <= param < end, plus user-provided dom facts
	domFacts := []FactStmt{
		NewSpecFactStmt(TruePure, Atom(glob.KeySymbolLessEqual), []Obj{stmt.start, Atom(stmt.param)}, stmt.Line),
		NewSpecFactStmt(TruePure, Atom(glob.KeySymbolLess), []Obj{Atom(stmt.param), stmt.end}, stmt.Line),
	}
	// Add user-provided dom facts
	domFacts = append(domFacts, stmt.DomFactsOrNil...)

	thenFacts := stmt.ThenFacts
	return NewUniFact(params, paramSets, domFacts, thenFacts, stmt.Line)
}
