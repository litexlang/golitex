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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"slices"
)

func EqualFact(left, right Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{left, right})
}

func (stmt *UniFactStmt) ParamInParamSetFacts(uniConMap map[string]Fc) []*SpecFactStmt {
	paramSetFacts := make([]*SpecFactStmt, len(stmt.Params))
	for i, param := range stmt.Params {
		paramSetFacts[i] = NewInFactWithParamFc(uniConMap[param], stmt.ParamSets[i])
	}
	return paramSetFacts
}

func ReverseSliceOfReversibleFacts(facts []Spec_OrFact) []Spec_OrFact {
	ret := []Spec_OrFact{}
	if len(facts) == 1 {
		reversed := facts[0].ReverseIsTrue()
		for _, fact := range reversed {
			ret = append(ret, fact)
		}
		return ret
	}

	specFactsInFacts := []*SpecFactStmt{}
	orFactsInFacts := []*OrStmt{}
	for _, fact := range facts {
		switch asFact := fact.(type) {
		case *SpecFactStmt:
			specFactsInFacts = append(specFactsInFacts, asFact)
		case *OrStmt:
			orFactsInFacts = append(orFactsInFacts, asFact)
		default:
			panic("ReverseSliceOfReversibleFacts: fact is not a spec fact or an or fact")
		}
	}

	reversedSpecFacts := make([]*SpecFactStmt, len(specFactsInFacts))
	for i, specFact := range specFactsInFacts {
		reversedSpecFacts[i] = specFact.ReverseTrue()
	}

	orFact_GotBYReversedSpecFacts := NewOrStmt(reversedSpecFacts)
	ret = append(ret, orFact_GotBYReversedSpecFacts)

	specFacts_GotByReversedOrFacts := []*SpecFactStmt{}
	for _, orFact := range orFactsInFacts {
		reversedOrFact := orFact.ReverseIsTrue()
		specFacts_GotByReversedOrFacts = append(specFacts_GotByReversedOrFacts, reversedOrFact...)
	}

	for _, specFact := range specFacts_GotByReversedOrFacts {
		ret = append(ret, specFact)
	}

	return ret
}

func NewEqualFact(left, right Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{left, right})
}

func IsFcFnWithHeadName(fc Fc, headName string) bool {
	fcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	headAtom, ok := fcFn.FnHead.(FcAtom)
	if !ok {
		return false
	}

	return string(headAtom) == headName
}

func IsFcFnWithHeadNameInSlice(fc Fc, headNames map[string]struct{}) bool {
	fcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	headAtom, ok := fcFn.FnHead.(FcAtom)
	if !ok {
		return false
	}

	_, ok = headNames[string(headAtom)]
	return ok
}

func (defHeader *DefHeader) GetInstantiatedParamInParamSetFact(uniMap map[string]Fc) ([]*SpecFactStmt, error) {
	paramSetFacts := make([]*SpecFactStmt, len(defHeader.Params))
	for i, param := range defHeader.Params {
		instantiatedSet, err := defHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		paramSetFacts[i] = NewInFactWithParamFc(uniMap[param], instantiatedSet)
	}
	return paramSetFacts, nil
}

func (stmt *UniFactStmt) ParamInParamSet() []*SpecFactStmt {
	paramSetFacts := make([]*SpecFactStmt, len(stmt.Params))
	for i, param := range stmt.Params {
		paramSetFacts[i] = NewInFactWithParamFc(FcAtom(param), stmt.ParamSets[i])
	}
	return paramSetFacts
}

func (stmt *EqualsFactStmt) ToEqualFacts() []*SpecFactStmt {
	ret := make([]*SpecFactStmt, len(stmt.Params)-1)
	for i := range len(stmt.Params) - 1 {
		ret[i] = NewEqualFact(stmt.Params[i], stmt.Params[i+1])
	}
	return ret
}

func (stmt *EqualsFactStmt) ToEqualFacts_PairwiseCombination() []*SpecFactStmt {
	ret := []*SpecFactStmt{}
	for i := range len(stmt.Params) - 1 {
		for j := i + 1; j < len(stmt.Params); j++ {
			ret = append(ret, NewEqualFact(stmt.Params[i], stmt.Params[j]))
		}
	}
	return ret
}

func (stmt *ClaimPropStmt) ToProp() *DefPropStmt {
	return NewDefPropStmt(&stmt.Prop.DefHeader, stmt.Prop.DomFacts, stmt.Prop.IffFacts, []FactStmt{})
}

func (strSlice StrSlice) ToFcSlice() []Fc {
	ret := make([]Fc, len(strSlice))
	for i, str := range strSlice {
		ret[i] = FcAtom(str)
	}
	return ret
}

func (head DefHeader) ToSpecFact() *SpecFactStmt {
	params := head.Params.ToFcSlice()
	return NewSpecFactStmt(TruePure, FcAtom(head.Name), params)
}

func (stmt *DefPropStmt) ToForallWhenPropIsTrue_Then_ThenSectionOfPropIsTrue() *UniFactStmt {
	return NewUniFact(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []FactStmt{stmt.DefHeader.ToSpecFact()}, stmt.ThenFacts)
}

func (stmt *DefExistPropStmt) ToProp() *SpecFactStmt {
	params := stmt.DefBody.DefHeader.Params.ToFcSlice()
	return NewSpecFactStmt(TruePure, FcAtom(stmt.DefBody.DefHeader.Name), params)
}

func (stmt *DefExistPropStmt) ToForallParamsSatisfyDomFacts_Then_ExistFactIsTrue() *UniFactStmt {
	return NewUniFact(stmt.ExistParams, stmt.ExistParamSets, stmt.DefBody.DomFacts, []FactStmt{stmt.ToProp()})
}

func (stmt *NamedUniFactStmt) ToUniFact() *UniFactStmt {
	return NewUniFact(stmt.DefPropStmt.DefHeader.Params, stmt.DefPropStmt.DefHeader.ParamSets, stmt.DefPropStmt.IffFacts, stmt.DefPropStmt.ThenFacts)
}

func (fcFn *FcFn) IsFcFn_HasAtomHead_ReturnHead() (FcAtom, bool) {
	head, ok := fcFn.FnHead.(FcAtom)
	if !ok {
		return "", false
	}
	return head, true
}

func (stmt *FnTemplateDefStmt) Instantiate_GetFnTemplateNoName(fc *FcFn) (*FnTStruct, error) {
	uniMap := map[string]Fc{}
	templateParams := stmt.TemplateDefHeader.Params
	if len(templateParams) != len(fc.Params) {
		return nil, fmt.Errorf("template params and fc params must have the same length")
	}

	for i, param := range templateParams {
		uniMap[param] = fc.Params[i]
	}

	instantiatedParamSets, err := stmt.Fn.ParamSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedDomFacts, err := stmt.Fn.DomFacts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedThenFacts, err := stmt.Fn.ThenFacts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedRetSet, err := stmt.Fn.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	return NewFnTStruct(stmt.Fn.Params, instantiatedParamSets, instantiatedRetSet, instantiatedDomFacts, instantiatedThenFacts), nil
}

func (fcFn *FcFn) HasHeadInSlice(headNames []string) bool {
	headAtom, ok := fcFn.FnHead.(FcAtom)
	if !ok {
		return false
	}
	return slices.Contains(headNames, string(headAtom))
}

func (fcAsFcFn *FcFn) FnTFc_ToFnTNoName() (*FnTStruct, error) {
	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("expected FcFn, but got %T", fcAsFcFn.FnHead)
	}

	if len(fcAsFcFn.Params) != 1 {
		return nil, fmt.Errorf("expected 1 param, but got %d", len(fcAsFcFn.Params))
	}

	randomParams := []string{}
	for range len(fcAsFcFnHeadAsFcFn.Params) {
		currentParam := glob.RandomString(4)
		if slices.Contains(randomParams, currentParam) {
			continue
		}
		randomParams = append(randomParams, currentParam)
	}

	paramSets := fcAsFcFnHeadAsFcFn.Params
	retSet := fcAsFcFn.Params[0]

	fnTNoName := NewFnTStruct(randomParams, paramSets, retSet, []FactStmt{}, []FactStmt{})

	return fnTNoName, nil
}

// 给定 f(a)(b,c)(e,d,f)，返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
func GetFnHeadChain_AndItSelf(fc Fc) ([]Fc, [][]Fc) {
	switch fc.(type) {
	case *FcFn:
		left, right := GetFnHeadChain_AndItSelf(fc.(*FcFn).FnHead)
		// return append(GetFnHeadChain_AndItSelf(fc.(*FcFn).FnHead), fc)
		return append(left, fc), append(right, append([]Fc{}, fc.(*FcFn).Params...))
	case FcAtom:
		return []Fc{fc}, nil
	default:
		panic("expected FcFn or FcAtom, but got " + fc.String())
	}
}

func (fcAsFcFn *FcFn) IsFnT_FcFn_Ret_ParamSets_And_RetSet(fc *FcFn) (bool, []Fc, Fc) {
	if !IsFnTemplate_FcFn(fcAsFcFn) {
		return false, nil, nil
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return false, nil, nil
	}

	paramSets := append(fcAsFcFnHeadAsFcFn.Params, fcAsFcFn.Params...)

	retSet := fcAsFcFn.Params[0]

	return true, paramSets, retSet
}

func MakeUniMap(freeParams []string, params []Fc) (map[string]Fc, error) {
	if len(freeParams) != len(params) {
		return nil, fmt.Errorf("free params length mismatch")
	}

	uniMap := map[string]Fc{}
	for i := range len(freeParams) {
		uniMap[freeParams[i]] = params[i]
	}
	return uniMap, nil
}
