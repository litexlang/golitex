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

	propSpecFact := NewPureSpecificFactStmt(true, Atom((defStmt.DefHeader.Name)), propSpecFactParams, defStmt.Line)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFactsOrNil...)

	propToIff := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, propToIffDomFacts, defStmt.IffFactsOrNil, defStmt.Line)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFactsOrNil...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFactsOrNil...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact}, defStmt.Line)

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Obj{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, Atom(param))
	}

	propSpecFact := NewPureSpecificFactStmt(true, Atom(defStmt.DefHeader.Name), propSpecFactParams, defStmt.Line)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFactsOrNil...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFactsOrNil...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact}, defStmt.Line)

	return IffToProp
}

// func (defStmt *DefExistPropStmt) ToSpecFact() *SpecFactStmt {
// 	propSpecFactParams := []Obj{}
// 	for _, param := range defStmt.DefBody.DefHeader.Params {
// 		propSpecFactParams = append(propSpecFactParams, Atom(param))
// 	}

// 	propSpecFact := NewSpecFactStmt(TruePure, Atom(defStmt.DefBody.DefHeader.Name), propSpecFactParams, defStmt.Line)

// 	return propSpecFact
// }

func (stmt *PureSpecificFactStmt) ReverseParameterOrder() (*PureSpecificFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Obj{stmt.Params[1], stmt.Params[0]}

	return NewPureSpecificFactStmt(stmt.IsTrue, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *PureSpecificFactStmt) IsValidEqualFact() (bool, error) {
	if string(stmt.PropName) == glob.KeySymbolEqual {
		if len(stmt.Params) == 2 {
			return true, nil
		} else {
			return false, fmt.Errorf("equal fact %s should have 2 params, but got %d", stmt.String(), len(stmt.Params))
		}
	} else {
		return false, nil
	}
}

func (stmt *PureSpecificFactStmt) IsBuiltinProp_ExceptEqual() bool {
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName)) && string(stmt.PropName) != glob.KeySymbolEqual
}

func NewInFact(param string, paramSet Obj) *PureSpecificFactStmt {
	switch string(paramSet.String()) {
	case glob.KeywordSet:
		return NewIsASetFact(Atom(param), glob.BuiltinLine0)
	case glob.KeywordFiniteSet:
		return NewIsAFiniteSetFact(Atom(param), glob.BuiltinLine0)
	case glob.KeywordNonEmptySet:
		return NewIsANonEmptySetFact(Atom(param), glob.BuiltinLine0)
	default:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIn), []Obj{Atom(param), paramSet}, glob.BuiltinLine0)
	}
}

func NewInFactWithParamObj(param Obj, paramSet Obj, line uint) *PureSpecificFactStmt {
	switch string(paramSet.String()) {
	case glob.KeywordSet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsASet), []Obj{param}, line)
	case glob.KeywordFiniteSet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsAFiniteSet), []Obj{param}, line)
	case glob.KeywordNonEmptySet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsANonEmptySet), []Obj{param}, line)
	default:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIn), []Obj{param, paramSet}, line)
	}
}

func NewInFactWithObj(param Obj, paramSet Obj) *PureSpecificFactStmt {
	switch string(paramSet.String()) {
	case glob.KeywordSet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsASet), []Obj{param}, glob.BuiltinLine0)
	case glob.KeywordFiniteSet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsAFiniteSet), []Obj{param}, glob.BuiltinLine0)
	case glob.KeywordNonEmptySet:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIsANonEmptySet), []Obj{param}, glob.BuiltinLine0)
	default:
		return NewPureSpecificFactStmt(true, Atom(glob.KeywordIn), []Obj{param, paramSet}, glob.BuiltinLine0)
	}
}

func IsFnSet(obj Obj) bool {
	objAsFnObj, ok := obj.(*FnObj)
	if !ok {
		return false
	}

	objHeadAsFnObj, ok := objAsFnObj.FnHead.(*FnObj)
	if !ok {
		return false
	}

	return IsAtomObjAndEqualToStr(objHeadAsFnObj.FnHead, glob.KeywordFn)
}

func (stmt *PureSpecificFactStmt) ReverseSpecFactParamsOrder() (*PureSpecificFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("ReverseSpecFactParamsOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Obj{stmt.Params[1], stmt.Params[0]}
	return NewPureSpecificFactStmt(stmt.IsTrue, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *DefLetStmt) NewInFacts() []*PureSpecificFactStmt {
	facts := []*PureSpecificFactStmt{}

	if len(stmt.Objs) != len(stmt.ObjSets) {
		panic("NewInFacts: len(stmt.Objs) != len(stmt.ObjSets)")
	}

	for i, obj := range stmt.Objs {
		paramSet := stmt.ObjSets[i]
		facts = append(facts, NewInFact(obj, paramSet))
	}

	return facts
}

func (defHeader *DefHeader) NewInFacts() []*PureSpecificFactStmt {
	facts := []*PureSpecificFactStmt{}
	for i, param := range defHeader.Params {
		facts = append(facts, NewInFact(param, defHeader.ParamSets[i]))
	}

	return facts
}

func Get_FnTemplate_InObjForm_ParamSetsAndRetSet(obj Obj) ([]Obj, Obj, bool) {
	// given obj must be a function
	objAsFnObj, ok := obj.(*FnObj)
	if !ok {
		return nil, nil, false
	}

	objAsFnObjHeadAsFnObj, ok := objAsFnObj.FnHead.(*FnObj)
	if !ok {
		return nil, nil, false
	}

	if len(objAsFnObj.Params) != 1 {
		return nil, nil, false
	}

	if !IsAtomObjAndEqualToStr(objAsFnObjHeadAsFnObj.FnHead, glob.KeywordFn) {
		return nil, nil, false
	}

	paramSets := []Obj{}
	paramSets = append(paramSets, objAsFnObjHeadAsFnObj.Params...)

	return paramSets, objAsFnObj.Params[0], true
}

func GetExistParamsAndFactParamsFromExistFactStmt(stmt *PureSpecificFactStmt) ([]Obj, []Obj) {
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

func MakeExistFactParamsSlice(existParams []Obj, paramsInFact []Obj) []Obj {
	lengthOfExistParams := len(existParams)

	factParams := []Obj{}
	factParams = append(factParams, Atom(fmt.Sprintf("%d", lengthOfExistParams)))
	factParams = append(factParams, existParams...)
	factParams = append(factParams, paramsInFact...)

	return factParams
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

func isObjWithObjFnHeadWithName(obj Obj, name string) bool {
	objAsFnObj, ok := obj.(*FnObj)
	if !ok {
		return false
	}

	objAsFnObjHeadAsFnObj, ok := objAsFnObj.FnHead.(*FnObj)
	if !ok {
		return false
	}

	return IsAtomObjAndEqualToStr(objAsFnObjHeadAsFnObj.FnHead, name)
}

func IsFnTemplate_ObjFn(objFn *FnObj) bool {
	return isObjWithObjFnHeadWithName(objFn, glob.KeywordFn)
}

func IsObjAtomEqualToGivenString(obj Obj, name string) bool {
	objAtom, ok := obj.(Atom)
	if !ok {
		return false
	}

	return string(objAtom) == name
}

func TransformEnumToUniFact(setName Obj, enumObjs []Obj) (*UniFactStmt, []*PureSpecificFactStmt, []*PureSpecificFactStmt) {
	freeObjName := Atom(glob.RandomString(4))
	equalFactsInOrFact := []*PureSpecificFactStmt{}
	itemsInSetFacts := []*PureSpecificFactStmt{}
	for _, obj := range enumObjs {
		equalFactsInOrFact = append(equalFactsInOrFact, NewPureSpecificFactStmt(true, Atom(glob.KeySymbolEqual), []Obj{freeObjName, obj}, glob.BuiltinLine0))
		itemsInSetFacts = append(itemsInSetFacts, NewPureSpecificFactStmt(true, Atom(glob.KeywordIn), []Obj{obj, setName}, glob.BuiltinLine0))
	}

	pairwiseNotEqualFacts := []*PureSpecificFactStmt{}
	for i := range len(enumObjs) {
		for j := range len(enumObjs) {
			if i == j {
				continue
			}
			pairwiseNotEqualFacts = append(pairwiseNotEqualFacts, NewPureSpecificFactStmt(false, Atom(glob.KeySymbolEqual), []Obj{enumObjs[i], enumObjs[j]}, glob.BuiltinLine0))
		}
	}

	orFact := NewOrStmt(equalFactsInOrFact, glob.BuiltinLine0)
	forallItemInSetEqualToOneOfGivenItems := NewUniFact([]string{string(freeObjName)}, []Obj{setName}, []FactStmt{}, []FactStmt{orFact}, glob.BuiltinLine0)

	return forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts
}

func (stmt *ProveForStmt) UniFact() *UniFactStmt {
	params := stmt.Params
	paramSets := make([]Obj, len(params))
	for i := range params {
		paramSets[i] = Atom(glob.KeywordInteger)
	}

	// Build dom facts based on range type for each parameter
	domFacts := []FactStmt{}
	for i, param := range params {
		left := stmt.Lefts[i]
		right := stmt.Rights[i]
		isRange := stmt.IsProveIRange[i]

		// left <= param
		domFacts = append(domFacts, NewPureSpecificFactStmt(true, Atom(glob.KeySymbolLessEqual), []Obj{left, Atom(param)}, stmt.Line))

		if isRange {
			// range: left <= param < right
			domFacts = append(domFacts, NewPureSpecificFactStmt(true, Atom(glob.KeySymbolLess), []Obj{Atom(param), right}, stmt.Line))
		} else {
			// closed_range: left <= param <= right
			domFacts = append(domFacts, NewPureSpecificFactStmt(true, Atom(glob.KeySymbolLessEqual), []Obj{Atom(param), right}, stmt.Line))
		}
	}
	// Add user-provided dom facts
	domFacts = append(domFacts, stmt.DomFacts...)

	thenFacts := stmt.ThenFacts
	return NewUniFact(params, paramSets, domFacts, thenFacts, stmt.Line)
}

func (stmt *PureSpecificFactStmt) ExistStFactToPropNameExistParamsParams() ([]Obj, []Obj) {
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

func (stmt *PureSpecificFactStmt) ExistStFactToPropNameExistParamsParamsAndTrueSpecFactAfterSt() ([]Obj, []Obj, *PureSpecificFactStmt) {
	lengthOfExistParams, _ := strconv.Atoi(string(stmt.Params[0].(Atom)))

	existParams := []Obj{}
	factParams := []Obj{}
	newSpecFactParams := []Obj{}
	for i := 1; i < lengthOfExistParams+1; i++ {
		existParams = append(existParams, stmt.Params[i])
	}

	for i := lengthOfExistParams + 1; i < len(stmt.Params); i++ {
		factParams = append(factParams, stmt.Params[i])
		newSpecFactParams = append(newSpecFactParams, stmt.Params[i])
	}

	newSpecFact := NewPureSpecificFactStmt(true, stmt.PropName, newSpecFactParams, glob.BuiltinLine0)

	return existParams, factParams, newSpecFact
}

// func (stmt *HaveObjStStmt) ToTruePurePropExistStFact() *SpecFactStmt {
// 	existStParams := MakeExistFactParamsSlice(stmt.ObjNames.ToObjSlice(), stmt.Fact.Params)
// 	return NewSpecFactStmt(TrueExist_St, stmt.Fact.PropName, existStParams, stmt.Line)
// }

func (stmt *HaveObjStStmt) ToTruePurePropExistStFact() *PureSpecificFactStmt {
	return NewExistStFact(TrueExist_St, stmt.Fact.PropName, stmt.Fact.IsTrue(), stmt.ObjNames, stmt.ObjSets, stmt.Fact.Params, stmt.Line)
}

func (stmt *WitnessStmt) ToTrueExistStFact() *PureSpecificFactStmt {
	return NewExistStFact(TrueExist_St, stmt.Fact.PropName, stmt.Fact.IsTrue(), stmt.ExistParams, stmt.ExistParamSets, stmt.Fact.Params, stmt.Line)
}
