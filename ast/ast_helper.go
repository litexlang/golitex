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
	"slices"
	"strconv"
	"strings"
)

func EqualFact(left, right Obj) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeySymbolEqual), []Obj{left, right}, glob.BuiltinLine0)
}

func (stmt *UniFactStmt) ParamInParamSetFacts(uniConMap map[string]Obj) []*SpecFactStmt {
	paramSetFacts := make([]*SpecFactStmt, len(stmt.Params))
	for i, param := range stmt.Params {
		paramSetFacts[i] = NewInFactWithParamObj(uniConMap[param], stmt.ParamSets[i], stmt.Line)
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

	orFact_GotBYReversedSpecFacts := NewOrStmt(reversedSpecFacts, glob.BuiltinLine0)
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

func NewEqualFact(left, right Obj) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeySymbolEqual), []Obj{left, right}, glob.BuiltinLine0)
}

func IsFn_WithHeadName(obj Obj, headName string) bool {
	fnObj, ok := obj.(*FnObj)
	if !ok {
		return false
	}

	headAtom, ok := fnObj.FnHead.(Atom)
	if !ok {
		return false
	}

	return string(headAtom) == headName
}

func IsFn_WithHeadNameInSlice(obj Obj, headNames map[string]struct{}) bool {
	fnObj, ok := obj.(*FnObj)
	if !ok {
		return false
	}

	headAtom, ok := fnObj.FnHead.(Atom)
	if !ok {
		return false
	}

	_, ok = headNames[string(headAtom)]
	return ok
}

func (defHeader *DefHeader) GetInstantiatedParamInParamSetFact(uniMap map[string]Obj) ([]*SpecFactStmt, error) {
	paramSetFacts := make([]*SpecFactStmt, len(defHeader.Params))
	for i, param := range defHeader.Params {
		instantiatedSet, err := defHeader.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		paramSetFacts[i] = NewInFactWithParamObj(uniMap[param], instantiatedSet, glob.BuiltinLine0)
	}
	return paramSetFacts, nil
}

func (stmt *UniFactStmt) ParamInParamSet() []*SpecFactStmt {
	paramSetFacts := make([]*SpecFactStmt, len(stmt.Params))
	for i, param := range stmt.Params {
		paramSetFacts[i] = NewInFactWithParamObj(Atom(param), stmt.ParamSets[i], stmt.Line)
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

func (stmt *ClaimImplicationStmt) ToProp() *DefPropStmt {
	return stmt.Implication.ToProp()
}

func (strSlice StrSlice) ToObjSlice() []Obj {
	ret := make([]Obj, len(strSlice))
	for i, str := range strSlice {
		ret[i] = Atom(str)
	}
	return ret
}

func (head DefHeader) ToSpecFact() *SpecFactStmt {
	params := head.Params.ToObjSlice()
	return NewSpecFactStmt(TruePure, Atom(head.Name), params, glob.BuiltinLine0)
}

func (stmt *DefPropStmt) ToForallWhenPropIsTrue_Then_ThenSectionOfPropIsTrue() *UniFactStmt {
	return NewUniFact(stmt.DefHeader.Params, stmt.DefHeader.ParamSets, []FactStmt{stmt.DefHeader.ToSpecFact()}, stmt.ImplicationFactsOrNil, glob.BuiltinLine0)
}

func (stmt *DefExistPropStmt) ToProp() *SpecFactStmt {
	params := stmt.DefBody.DefHeader.Params.ToObjSlice()
	return NewSpecFactStmt(TruePure, Atom(stmt.DefBody.DefHeader.Name), params, glob.BuiltinLine0)
}

func (stmt *DefExistPropStmt) ToForallParamsSatisfyDomFacts_Then_ExistFactIsTrue() *UniFactStmt {
	return NewUniFact(stmt.ExistParams, stmt.ExistParamSets, stmt.DefBody.DomFactsOrNil, []FactStmt{stmt.ToProp()}, glob.BuiltinLine0)
}

// func (stmt *NamedUniFactStmt) ToUniFact() *UniFactStmt {
// 	return NewUniFact(stmt.DefPropStmt.DefHeader.Params, stmt.DefPropStmt.DefHeader.ParamSets, stmt.DefPropStmt.IffFactsOrNil, stmt.DefPropStmt.ImplicationFactsOrNil, glob.BuiltinLine)
// }

func (objFn *FnObj) IsObjFn_HasAtomHead_ReturnHead() (Atom, bool) {
	head, ok := objFn.FnHead.(Atom)
	if !ok {
		return "", false
	}
	return head, true
}

func (stmt *DefFnSetStmt) Instantiate_GetFnTemplateNoName(fnObj *FnObj) (*FnTemplate, error) {
	uniMap := map[string]Obj{}
	templateParams := stmt.TemplateDefHeader.Params
	if len(templateParams) != len(fnObj.Params) {
		return nil, fmt.Errorf("template params and obj params must have the same length")
	}

	for i, param := range templateParams {
		uniMap[param] = fnObj.Params[i]
	}

	instantiatedParamSets, err := stmt.Fn.ParamSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedDomFacts, err := stmt.Fn.DomFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedThenFacts, err := stmt.Fn.ThenFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedRetSet, err := stmt.Fn.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	return NewFnTStruct(stmt.Fn.Params, instantiatedParamSets, instantiatedRetSet, instantiatedDomFacts, instantiatedThenFacts, stmt.Line), nil
}

func (objFn *FnObj) HasHeadInSlice(headNames []string) bool {
	headAtom, ok := objFn.FnHead.(Atom)
	if !ok {
		return false
	}
	return slices.Contains(headNames, string(headAtom))
}

func (objAsFnObj *FnObj) FnTObj_ToFnTNoName() (*FnTemplate, error) {
	objAsFnObjHeadAsFnObj, ok := objAsFnObj.FnHead.(*FnObj)
	if !ok {
		return nil, fmt.Errorf("expected ObjFn, but got %T", objAsFnObj.FnHead)
	}

	if len(objAsFnObj.Params) != 1 {
		return nil, fmt.Errorf("expected 1 param, but got %d", len(objAsFnObj.Params))
	}

	randomParams := []string{}
	for range len(objAsFnObjHeadAsFnObj.Params) {
		currentParam := glob.RandomString(4)
		if slices.Contains(randomParams, currentParam) {
			continue
		}
		randomParams = append(randomParams, currentParam)
	}

	paramSets := objAsFnObjHeadAsFnObj.Params
	retSet := objAsFnObj.Params[0]

	fnTNoName := NewFnTStruct(randomParams, paramSets, retSet, []FactStmt{}, []FactStmt{}, glob.BuiltinLine0)

	return fnTNoName, nil
}

// 给定 f(a)(b,c)(e,d,f)，返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
func GetFnHeadChain_AndItSelf(obj Obj) ([]Obj, [][]Obj) {
	switch asObj := obj.(type) {
	case *FnObj:
		left, right := GetFnHeadChain_AndItSelf(asObj.FnHead)
		// return append(GetFnHeadChain_AndItSelf(obj.(*FnObj).FnHead), obj)
		return append(left, obj), append(right, append([]Obj{}, asObj.Params...))
	case Atom:
		return []Obj{obj}, [][]Obj{nil}
	default:
		panic("expected FnObj or AtomObj, but got " + obj.String())
	}
}

func (objAsFnObj *FnObj) GetParamSetsAndRetSetOfAnonymousFn(fnObj *FnObj) (bool, []Obj, Obj) {
	if !IsFnTemplate_ObjFn(objAsFnObj) {
		return false, nil, nil
	}

	objAsFnObjHeadAsFnObj, ok := objAsFnObj.FnHead.(*FnObj)
	if !ok {
		return false, nil, nil
	}

	paramSets := append([]Obj{}, objAsFnObjHeadAsFnObj.Params...)

	retSet := objAsFnObj.Params[0]

	return true, paramSets, retSet
}

func MakeUniMap(freeParams []string, params []Obj) (map[string]Obj, error) {
	if len(freeParams) != len(params) {
		return nil, fmt.Errorf("free params length mismatch")
	}

	uniMap := map[string]Obj{}
	for i := range len(freeParams) {
		uniMap[freeParams[i]] = params[i]
	}
	return uniMap, nil
}

func InstFacts(facts []FactStmt, uniMap map[string]Obj) ([]FactStmt, error) {
	newFacts := make([]FactStmt, len(facts))
	for i, fact := range facts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newFacts[i] = newFact
	}
	return newFacts, nil
}

func AnonymousFnToInstFnTemplate(objFnTypeT *FnObj) (*FnTemplate, bool) {
	ok, paramSets, retSet := objFnTypeT.GetParamSetsAndRetSetOfAnonymousFn(objFnTypeT)
	if !ok {
		return nil, false
	}

	excelNames := glob.GenerateNamesLikeExcelColumnNames(len(paramSets))
	return NewFnTStruct(excelNames, paramSets, retSet, []FactStmt{}, []FactStmt{}, glob.BuiltinLine0), true
}

func UnknownFactMsg(fact FactStmt) string {
	return fmt.Sprintf("%s\nis unknown\n", fact)
}

func ToInt(obj Obj) (int, bool) {
	atomObj, ok := obj.(Atom)
	if !ok {
		return 0, false
	}

	// string to int
	num, err := strconv.Atoi(string(atomObj))
	if err != nil {
		return 0, false
	}
	return num, true
}

func ExtractParamsFromFact(fact FactStmt) []string {
	switch asFact := fact.(type) {
	case *UniFactStmt:
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

func SimplifyDimCart(obj *FnObj) (Obj, bool) {
	if IsAtomObjAndEqualToStr(obj.FnHead, glob.KeywordSetDim) {
		if len(obj.Params) == 1 && IsFn_WithHeadName(obj.Params[0], glob.KeywordCart) {
			cartObj := obj.Params[0].(*FnObj)
			dimValue := len(cartObj.Params)
			return Atom(fmt.Sprintf("%d", dimValue)), true
		}
	}
	return nil, false
}

func SimplifyProjCart(obj *FnObj) (Obj, bool) {
	if IsAtomObjAndEqualToStr(obj.FnHead, glob.KeywordProj) {
		if len(obj.Params) == 2 && IsFn_WithHeadName(obj.Params[0], glob.KeywordCart) {
			cartObj := obj.Params[0].(*FnObj)
			index, ok := ToInt(obj.Params[1])
			if ok && index >= 1 && index <= len(cartObj.Params) {
				// proj 的索引是从 1 开始的，所以需要减 1
				return cartObj.Params[index-1], true
			}
		}
	}
	return nil, false
}

func (factSlice FactStmtSlice) Copy() FactStmtSlice {
	newFactSlice := make([]FactStmt, len(factSlice))
	copy(newFactSlice, factSlice)
	return newFactSlice
}

func MakeListSetObj(params []Obj) Obj {
	return NewFnObj(Atom(glob.KeywordListSet), params)
}

func MakeSetBuilderObj(param string, parentSet Obj, facts SpecFactPtrSlice) (*FnObj, error) {
	params := []Obj{Atom(param), parentSet}

	for _, fact := range facts {
		atoms, err := changeSpecFactIntoObjs(fact)
		if err != nil {
			return nil, err
		}
		params = append(params, atoms...)
	}

	return NewFnObj(Atom(glob.KeywordSetBuilder), params), nil
}

func changeSpecFactIntoObjs(fact *SpecFactStmt) ([]Obj, error) {
	ret := []Obj{}
	switch fact.TypeEnum {
	case FalsePure:
		ret = append(ret, Atom(strconv.Itoa(int(FalsePure))))
	case FalseExist_St:
		ret = append(ret, Atom(strconv.Itoa(int(FalseExist_St))))
	case TrueExist_St:
		ret = append(ret, Atom(strconv.Itoa(int(TrueExist_St))))
	case TruePure:
		ret = append(ret, Atom(strconv.Itoa(int(TruePure))))
	}
	ret = append(ret, Atom(strconv.Itoa(len(fact.Params))))
	ret = append(ret, fact.PropName)

	for _, param := range fact.Params {
		ret = append(ret, param)
	}

	return ret, nil
}

func IsTupleObj(obj Obj) bool {
	if asFnObj, ok := obj.(*FnObj); ok {
		return IsTupleFnObj(asFnObj)
	}
	return false
}

func IsTupleFnObj(f *FnObj) bool {
	return f.FnHead.String() == glob.KeywordTuple
}

func IsIndexOptFnObj(f *FnObj) bool {
	return f.FnHead.String() == glob.KeywordObjAtIndexOpt
}

func IsListSetObj(obj Obj) bool {
	if asEnumStmt, ok := obj.(*FnObj); ok {
		return asEnumStmt.FnHead.String() == glob.KeywordListSet
	}
	return false
}

func NegateObj(right Obj) Obj {
	return NewFnObj(Atom(glob.KeySymbolStar), []Obj{Atom("-1"), right})
}

func NewIsANonEmptySetFact(param Obj, line uint) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIsANonEmptySet), []Obj{param}, line)
}

func NewIsAFiniteSetFact(param Obj, line uint) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIsAFiniteSet), []Obj{param}, line)
}

func NewIsASetFact(param Obj, line uint) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, Atom(glob.KeywordIsASet), []Obj{param}, line)
}

func ObjIsKeywordSetOrNonEmptySetOrFiniteSet(obj Obj) bool {
	if asAtom, ok := obj.(Atom); ok {
		return glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom))
	}
	return false
}

func ObjIsKeywordSet(obj Obj) bool {
	if asAtom, ok := obj.(Atom); ok {
		return string(asAtom) == glob.KeywordSet
	}
	return false
}

func ObjIsRangeOrClosedRangeWith2Params(obj Obj) bool {
	if asAtom, ok := obj.(*FnObj); ok {
		if len(asAtom.Params) != 2 {
			return false
		}

		return asAtom.FnHead.String() == glob.KeywordRange || asAtom.FnHead.String() == glob.KeywordClosedRange
	}
	return false
}

func IsTrueEqualFact(fact *SpecFactStmt) bool {
	if fact.TypeEnum != TruePure {
		return false
	}

	if fact.PropName != glob.KeySymbolEqual {
		return false
	}

	return true
}

func (stmt *ImplicationStmt) ToProp() *DefPropStmt {
	return NewDefPropStmt(stmt.DefHeader, stmt.DomFacts, nil, stmt.ImplicationFacts, stmt.Line)
}

func IsTrueSpecFactWithPropName(specFact *SpecFactStmt, propName string) bool {
	if specFact.TypeEnum != TruePure {
		return false
	}

	return string(specFact.PropName) == propName
}

func IsFalseSpecFactWithPropName(specFact *SpecFactStmt, propName string) bool {
	if specFact.TypeEnum != FalsePure {
		return false
	}

	return string(specFact.PropName) == propName
}

func GetParamSetsAndRetSetFromFnSet(fnSet *FnObj) ([]Obj, Obj, error) {
	retSet := fnSet.Params[0]

	paramSets := []Obj{}
	fnHeadAsFnObj, ok := fnSet.FnHead.(*FnObj)
	if !ok {
		return nil, nil, fmt.Errorf("expected FnObj, but got %T", fnSet.FnHead)
	}

	paramSets = append(paramSets, fnHeadAsFnObj.Params...)

	return paramSets, retSet, nil
}

func GetTupleValueAtIndex(tuple *FnObj, index Obj) Obj {
	if asAtom, ok := index.(Atom); ok {
		// string(asAtom) 是整数
		index, err := strconv.Atoi(string(asAtom))
		if err != nil {
			return nil
		}

		if index >= 1 && index <= len(tuple.Params) {
			return tuple.Params[index-1]
		}

		return nil
	}

	return nil
}

func (fnObj *FnObj) IsAtomHeadEqualToStr(s string) bool {
	if asAtom, ok := fnObj.FnHead.(Atom); ok {
		return string(asAtom) == s
	}

	return false
}

var BuiltinAndKernelDefinedNames = map[string]struct{}{}

func IsBuiltinOrKernelDefinedName(name string) bool {
	if glob.IsKeyword(name) || glob.IsKeySymbol(name) {
		return true
	}

	if glob.IsNumLitStr(name) {
		return true
	}

	_, ok := BuiltinAndKernelDefinedNames[name]
	return ok
}

func AddPkgNameToName(pkgName string, name string) string {
	if pkgName == "" {
		return name
	}
	return fmt.Sprintf("%s.%s", pkgName, name)
}

func ObjContainsFreeParams(obj Obj, freeParams []string) bool {
	switch asObj := obj.(type) {
	case *FnObj:
		return fnObjContainsFreeParams(asObj, freeParams)
	case Atom:
		return slices.Contains(freeParams, string(asObj))
	default:
		return false
	}
}

func fnObjContainsFreeParams(fnObj *FnObj, freeParams []string) bool {
	for _, param := range fnObj.Params {
		if ObjContainsFreeParams(param, freeParams) {
			return true
		}
	}
	if ObjContainsFreeParams(fnObj.FnHead, freeParams) {
		return true
	}
	return false
}
