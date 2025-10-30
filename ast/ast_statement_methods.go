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

func (stmt *SpecificFactStmt) IsBuiltinInfixRelaProp() bool {
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName))
}

func (stmt *UniFactWithIffStmt) NewUniFactWithThenToIff() *ForallFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.IffFacts, stmt.UniFact.Line)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.UniFact.ThenFacts...)
	return newUniFact
}

func (stmt *UniFactWithIffStmt) NewUniFactWithIffToThen() *ForallFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.UniFact.ThenFacts, stmt.UniFact.Line)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.IffFacts...)
	return newUniFact
}

func MergeOuterInnerUniFacts(outer *ForallFactStmt, inner *ForallFactStmt) *ForallFactStmt {
	newOuter := NewUniFact(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, outer.Line)

	newOuter.Params = append(newOuter.Params, inner.Params...)
	newOuter.ParamSets = append(newOuter.ParamSets, inner.ParamSets...)
	newOuter.DomFacts = append(newOuter.DomFacts, inner.DomFacts...)

	if len(newOuter.Params) != len(newOuter.ParamSets) {
		return nil
	}

	return newOuter
}

func (defStmt *DefPropStmt) Make_PropToIff_IffToProp() (*ForallFactStmt, *ForallFactStmt, error) {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

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

func (defStmt *DefPropStmt) IffToPropUniFact() *ForallFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact}, defStmt.Line)

	return IffToProp
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecificFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	return propSpecFact
}

func (defStmt *DefExistPropStmt) ToSpecFact() *SpecificFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefBody.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefBody.DefHeader.Name), propSpecFactParams, defStmt.Line)

	return propSpecFact
}

func (stmt *SpecificFactStmt) ReverseParameterOrder() (*SpecificFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *SpecificFactStmt) IsValidEqualFact() (bool, error) {
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

func (stmt *SpecificFactStmt) IsBuiltinProp_ExceptEqual() bool {
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName)) && !stmt.NameIs(glob.KeySymbolEqual)
}

// func (stmt *SpecFactStmt) IsMathInductionFact() bool {
// 	return string(stmt.PropName) == glob.KeywordProveByMathInduction
// }

func NewInFact(param string, paramSet Fc) *SpecificFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{FcAtom(param), paramSet}, glob.InnerGenLine)
}

func NewInFactWithParamFc(param Fc, paramSet Fc) *SpecificFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{param, paramSet}, glob.InnerGenLine)
}

func NewInFactWithFc(param Fc, paramSet Fc) *SpecificFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{param, paramSet}, glob.InnerGenLine)
}

func IsFnSet(fc Fc) bool {
	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	fcHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return false
	}

	return IsFcAtomAndEqualToStr(fcHeadAsFcFn.FnHead, glob.KeywordFn)
}

func (stmt *SpecificFactStmt) ReverseSpecFactParamsOrder() (*SpecificFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("ReverseSpecFactParamsOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}
	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *DefLetStmt) NewInFacts() []*SpecificFactStmt {
	facts := []*SpecificFactStmt{}

	if len(stmt.Objs) != len(stmt.ObjSets) {
		panic("NewInFacts: len(stmt.Objs) != len(stmt.ObjSets)")
	}

	for i, obj := range stmt.Objs {
		paramSet := stmt.ObjSets[i]
		facts = append(facts, NewInFact(obj, paramSet))
	}

	return facts
}

func (defHeader *DefHeader) NewInFacts() []*SpecificFactStmt {
	facts := []*SpecificFactStmt{}
	for i, param := range defHeader.Params {
		facts = append(facts, NewInFact(param, defHeader.ParamSets[i]))
	}

	return facts
}

func Get_FnTemplate_InFcForm_ParamSetsAndRetSet(fc Fc) ([]Fc, Fc, bool) {
	// given fc must be a function
	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, nil, false
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return nil, nil, false
	}

	if len(fcAsFcFn.Params) != 1 {
		return nil, nil, false
	}

	if !IsFcAtomAndEqualToStr(fcAsFcFnHeadAsFcFn.FnHead, glob.KeywordFn) {
		return nil, nil, false
	}

	paramSets := []Fc{}
	paramSets = append(paramSets, fcAsFcFnHeadAsFcFn.Params...)

	return paramSets, fcAsFcFn.Params[0], true
}

func MakeExistFactParamsSlice(existParams []Fc, paramsInFact []Fc) []Fc {
	lengthOfExistParams := len(existParams)

	factParams := []Fc{}
	factParams = append(factParams, FcAtom(fmt.Sprintf("%d", lengthOfExistParams)))
	factParams = append(factParams, existParams...)
	factParams = append(factParams, paramsInFact...)

	return factParams
}

func GetExistFactExistParamsAndFactParams(stmt *SpecificFactStmt) ([]Fc, []Fc) {
	lengthOfExistParams, _ := strconv.Atoi(string(stmt.Params[0].(FcAtom)))

	existParams := []Fc{}
	factParams := []Fc{}
	for i := 1; i < lengthOfExistParams+1; i++ {
		existParams = append(existParams, stmt.Params[i])
	}

	for i := lengthOfExistParams + 1; i < len(stmt.Params); i++ {
		factParams = append(factParams, stmt.Params[i])
	}

	return existParams, factParams
}

func (factStmtSlice FactStmtSlice) Instantiate(uniMap map[string]Fc) (FactStmtSlice, error) {
	instantiatedFacts := FactStmtSlice{}
	for _, fact := range factStmtSlice {
		instantiatedFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedFacts = append(instantiatedFacts, instantiatedFact)
	}
	return instantiatedFacts, nil
}

func isFcWithFcFnHeadWithName(fc Fc, name string) bool {
	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return false
	}

	return IsFcAtomAndEqualToStr(fcAsFcFnHeadAsFcFn.FnHead, name)
}

func IsFnTemplate_FcFn(fcFn *FcFn) bool {
	return isFcWithFcFnHeadWithName(fcFn, glob.KeywordFn)
}

func IsFcAtomEqualToGivenString(fc Fc, name string) bool {
	fcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	return string(fcAtom) == name
}

func TransformEnumToUniFact(setName Fc, enumFcs []Fc) (*ForallFactStmt, []*SpecificFactStmt, []*SpecificFactStmt) {
	freeObjName := FcAtom(glob.RandomString(4))
	equalFactsInOrFact := []*SpecificFactStmt{}
	itemsInSetFacts := []*SpecificFactStmt{}
	for _, fc := range enumFcs {
		equalFactsInOrFact = append(equalFactsInOrFact, NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{freeObjName, fc}, glob.InnerGenLine))
		itemsInSetFacts = append(itemsInSetFacts, NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{fc, setName}, glob.InnerGenLine))
	}

	pairwiseNotEqualFacts := []*SpecificFactStmt{}
	for i := range len(enumFcs) {
		for j := range len(enumFcs) {
			if i == j {
				continue
			}
			pairwiseNotEqualFacts = append(pairwiseNotEqualFacts, NewSpecFactStmt(FalsePure, FcAtom(glob.KeySymbolEqual), []Fc{enumFcs[i], enumFcs[j]}, glob.InnerGenLine))
		}
	}

	orFact := NewOrStmt(equalFactsInOrFact, glob.InnerGenLine)
	forallItemInSetEqualToOneOfGivenItems := NewUniFact([]string{string(freeObjName)}, []Fc{setName}, []FactStmt{}, []FactStmt{orFact}, glob.InnerGenLine)

	return forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts
}

func (stmt *IntensionalSetStmt) ToEquivalentUniFacts() (*ForallFactStmt, *ForallFactStmt, error) {
	leftDomFacts := []FactStmt{}
	for _, proof := range stmt.Facts {
		leftDomFacts = append(leftDomFacts, proof)
	}

	leftUniFact := NewUniFact([]string{stmt.Param}, []Fc{stmt.ParentSet}, leftDomFacts, []FactStmt{NewInFact(stmt.Param, stmt.CurSet)}, glob.InnerGenLine)

	rightThenFacts := []FactStmt{NewInFact(stmt.Param, stmt.ParentSet)}
	for _, proof := range stmt.Facts {
		rightThenFacts = append(rightThenFacts, proof)
	}

	rightUniFact := NewUniFact([]string{stmt.Param}, []Fc{stmt.CurSet}, []FactStmt{}, rightThenFacts, glob.InnerGenLine)

	return leftUniFact, rightUniFact, nil
}

func (stmt *HaveSetFnStmt) ToDefFnStmt() *DefFnStmt {
	return NewDefFnStmt(string(stmt.DefHeader.Name), NewFnTStruct(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, FcAtom(glob.KeywordSet), []FactStmt{}, []FactStmt{stmt.ToIntensionalSetStmt()}, stmt.Line), stmt.Line)
}

func (stmt *HaveSetFnStmt) ToIntensionalSetStmt() *IntensionalSetStmt {
	params := []Fc{}
	for _, param := range stmt.DefHeader.Params {
		params = append(params, FcAtom(param))
	}

	fnName := FcAtom(stmt.DefHeader.Name)
	curSet := NewFcFn(fnName, params)
	intensionalSetStmt := NewIntensionalSetStmt(curSet, stmt.Param, stmt.ParentSet, stmt.Proofs, stmt.Line)

	return intensionalSetStmt
}

func (stmt *ProveInRangeStmt) UniFact() *ForallFactStmt {
	return NewUniFact([]string{stmt.Param}, []Fc{stmt.IntensionalSet}, []FactStmt{}, stmt.ThenFacts, stmt.Line)
}
