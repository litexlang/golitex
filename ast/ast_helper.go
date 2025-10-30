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
	"slices"
	"strconv"
	"strings"
)

func EqualFact(left, right Fc) *SpecificFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{left, right}, glob.InnerGenLine)
}

func (stmt *ForallFactStmt) ParamInParamSetFacts(uniConMap map[string]Fc) []*SpecificFactStmt {
	paramSetFacts := make([]*SpecificFactStmt, len(stmt.Params))
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

	specFactsInFacts := []*SpecificFactStmt{}
	orFactsInFacts := []*OrStmt{}
	for _, fact := range facts {
		switch asFact := fact.(type) {
		case *SpecificFactStmt:
			specFactsInFacts = append(specFactsInFacts, asFact)
		case *OrStmt:
			orFactsInFacts = append(orFactsInFacts, asFact)
		default:
			panic("ReverseSliceOfReversibleFacts: fact is not a spec fact or an or fact")
		}
	}

	reversedSpecFacts := make([]*SpecificFactStmt, len(specFactsInFacts))
	for i, specFact := range specFactsInFacts {
		reversedSpecFacts[i] = specFact.ReverseTrue()
	}

	orFact_GotBYReversedSpecFacts := NewOrStmt(reversedSpecFacts, glob.InnerGenLine)
	ret = append(ret, orFact_GotBYReversedSpecFacts)

	specFacts_GotByReversedOrFacts := []*SpecificFactStmt{}
	for _, orFact := range orFactsInFacts {
		reversedOrFact := orFact.ReverseIsTrue()
		specFacts_GotByReversedOrFacts = append(specFacts_GotByReversedOrFacts, reversedOrFact...)
	}

	for _, specFact := range specFacts_GotByReversedOrFacts {
		ret = append(ret, specFact)
	}

	return ret
}

func NewEqualFact(left, right Fc) *SpecificFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{left, right}, glob.InnerGenLine)
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

func (defHeader *DefHeader) GetInstantiatedParamInParamSetFact(uniMap map[string]Fc) ([]*SpecificFactStmt, error) {
	paramSetFacts := make([]*SpecificFactStmt, len(defHeader.Params))
	for i, param := range defHeader.Params {
		instantiatedSet, err := defHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		paramSetFacts[i] = NewInFactWithParamFc(uniMap[param], instantiatedSet)
	}
	return paramSetFacts, nil
}

func (stmt *ForallFactStmt) ParamInParamSet() []*SpecificFactStmt {
	paramSetFacts := make([]*SpecificFactStmt, len(stmt.Params))
	for i, param := range stmt.Params {
		paramSetFacts[i] = NewInFactWithParamFc(FcAtom(param), stmt.ParamSets[i])
	}
	return paramSetFacts
}

func (stmt *EqualsFactStmt) ToEqualFacts() []*SpecificFactStmt {
	ret := make([]*SpecificFactStmt, len(stmt.Params)-1)
	for i := range len(stmt.Params) - 1 {
		ret[i] = NewEqualFact(stmt.Params[i], stmt.Params[i+1])
	}
	return ret
}

func (stmt *EqualsFactStmt) ToEqualFacts_PairwiseCombination() []*SpecificFactStmt {
	ret := []*SpecificFactStmt{}
	for i := range len(stmt.Params) - 1 {
		for j := i + 1; j < len(stmt.Params); j++ {
			ret = append(ret, NewEqualFact(stmt.Params[i], stmt.Params[j]))
		}
	}
	return ret
}

func (stmt *ClaimPropStmt) ToProp() *DefPropStmt {
	return NewDefPropStmt(stmt.Prop.DefHeader, stmt.Prop.DomFacts, stmt.Prop.IffFacts, []FactStmt{}, stmt.GetLine())
}

func (strSlice StrSlice) ToFcSlice() []Fc {
	ret := make([]Fc, len(strSlice))
	for i, str := range strSlice {
		ret[i] = FcAtom(str)
	}
	return ret
}

func (head DefHeader) ToSpecFact() *SpecificFactStmt {
	params := head.Params.ToFcSlice()
	return NewSpecFactStmt(TruePure, FcAtom(head.Name), params, glob.InnerGenLine)
}

func (stmt *DefPropStmt) ToForallWhenPropIsTrue_Then_ThenSectionOfPropIsTrue() *ForallFactStmt {
	return NewUniFact(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []FactStmt{stmt.DefHeader.ToSpecFact()}, stmt.ThenFacts, glob.InnerGenLine)
}

func (stmt *DefExistPropStmt) ToProp() *SpecificFactStmt {
	params := stmt.DefBody.DefHeader.Params.ToFcSlice()
	return NewSpecFactStmt(TruePure, FcAtom(stmt.DefBody.DefHeader.Name), params, glob.InnerGenLine)
}

func (stmt *DefExistPropStmt) ToForallParamsSatisfyDomFacts_Then_ExistFactIsTrue() *ForallFactStmt {
	return NewUniFact(stmt.ExistParams, stmt.ExistParamSets, stmt.DefBody.DomFacts, []FactStmt{stmt.ToProp()}, glob.InnerGenLine)
}

func (stmt *NamedUniFactStmt) ToUniFact() *ForallFactStmt {
	return NewUniFact(stmt.DefPropStmt.DefHeader.Params, stmt.DefPropStmt.DefHeader.ParamSets, stmt.DefPropStmt.IffFacts, stmt.DefPropStmt.ThenFacts, glob.InnerGenLine)
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

	return NewFnTStruct(stmt.Fn.Params, instantiatedParamSets, instantiatedRetSet, instantiatedDomFacts, instantiatedThenFacts, stmt.Line), nil
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

	fnTNoName := NewFnTStruct(randomParams, paramSets, retSet, []FactStmt{}, []FactStmt{}, glob.InnerGenLine)

	return fnTNoName, nil
}

// 给定 f(a)(b,c)(e,d,f)，返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
func GetFnHeadChain_AndItSelf(fc Fc) ([]Fc, [][]Fc) {
	switch asFc := fc.(type) {
	case *FcFn:
		left, right := GetFnHeadChain_AndItSelf(asFc.FnHead)
		// return append(GetFnHeadChain_AndItSelf(fc.(*FcFn).FnHead), fc)
		return append(left, fc), append(right, append([]Fc{}, asFc.Params...))
	case FcAtom:
		return []Fc{fc}, [][]Fc{nil}
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

	paramSets := append([]Fc{}, fcAsFcFnHeadAsFcFn.Params...)

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

func InstFacts(facts []FactStmt, uniMap map[string]Fc) ([]FactStmt, error) {
	newFacts := make([]FactStmt, len(facts))
	for i, fact := range facts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newFacts[i] = newFact
	}
	return newFacts, nil
}

func FcFnT_To_FnTStruct(fcFnTypeT *FcFn) (*FnTStruct, bool) {
	ok, paramSets, retSet := fcFnTypeT.IsFnT_FcFn_Ret_ParamSets_And_RetSet(fcFnTypeT)
	if !ok {
		return nil, false
	}

	excelNames := glob.GenerateNamesLikeExcelColumnNames(len(paramSets))
	return NewFnTStruct(excelNames, paramSets, retSet, []FactStmt{}, []FactStmt{}, glob.InnerGenLine), true
}

func UnknownFactMsg(fact FactStmt) string {
	return fmt.Sprintf("%s\nis unknown\n", fact)
}

func ToInt(fc Fc) (int, bool) {
	fcAsFcInt, ok := fc.(FcAtom)
	if !ok {
		return 0, false
	}

	// string to int
	num, err := strconv.Atoi(string(fcAsFcInt))
	if err != nil {
		return 0, false
	}
	return num, true
}

// func (stmt *ProveInRange2tmt) UniFact() *UniFactStmt {
// 	params := []string{stmt.Param}
// 	paramSets := []Fc{FcAtom(glob.KeywordInteger)}
// 	largerEqualThanLeft := NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolLargerEqual), []Fc{FcAtom(stmt.Param), FcAtom(fmt.Sprintf("%d", stmt.Start))}, stmt.Line)
// 	smallerThanRight := NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolLess), []Fc{FcAtom(stmt.Param), FcAtom(fmt.Sprintf("%d", stmt.End))}, stmt.Line)
// 	domFacts := []FactStmt{largerEqualThanLeft, smallerThanRight}
// 	for _, fact := range stmt.DomFacts {
// 		domFacts = append(domFacts, fact)
// 	}
// 	thenFacts := stmt.ThenFacts
// 	return NewUniFact(params, paramSets, domFacts, thenFacts, stmt.Line)
// }

func ExtractParamsFromFact(fact FactStmt) []string {
	switch asFact := fact.(type) {
	case *ForallFactStmt:
		return asFact.Params
	case *UniFactWithIffStmt:
		return asFact.UniFact.Params
	default:
		return nil
	}
}

func HeaderWithParamsAndParamSetsString(header *DefHeader) string {
	var builder strings.Builder
	builder.WriteString(string(header.Name))
	builder.WriteString("(")
	paramParamSetsPairs := make([]string, len(header.Params))
	for i, param := range header.Params {
		paramParamSetsPairs[i] = fmt.Sprintf("%s %s", param, header.ParamSets[i].String())
	}
	builder.WriteString(strings.Join(paramParamSetsPairs, ", "))
	builder.WriteString(")")
	return builder.String()
}
