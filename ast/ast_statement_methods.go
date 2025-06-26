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
	"strconv"
	"strings"
)

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	// return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name)
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName))
}

func (stmt *UniFactWithIffStmt) NewUniFactWithThenToIff() *UniFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.IffFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.UniFact.ThenFacts...)
	return newUniFact
}

func (stmt *UniFactWithIffStmt) NewUniFactWithIffToThen() *UniFactStmt {
	newUniFact := NewUniFact(stmt.UniFact.Params, stmt.UniFact.ParamSets, stmt.UniFact.DomFacts, stmt.UniFact.ThenFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.IffFacts...)
	return newUniFact
}

func MergeOuterInnerUniFacts(outer *UniFactStmt, inner *UniFactStmt) *UniFactStmt {
	newOuter := NewUniFact(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts)

	newOuter.Params = append(newOuter.Params, inner.Params...)
	newOuter.ParamSets = append(newOuter.ParamSets, inner.ParamSets...)
	newOuter.DomFacts = append(newOuter.DomFacts, inner.DomFacts...)

	if len(newOuter.Params) != len(newOuter.ParamSets) {
		return nil
	}

	return newOuter
}

func (defStmt *DefPropStmt) Make_PropToIff_IffToProp() (*UniFactStmt, *UniFactStmt, error) {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, propToIffDomFacts, defStmt.IffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact})

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.ParamSets, IffToPropDomFacts, []FactStmt{propSpecFact})

	return IffToProp
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefHeader.Name), propSpecFactParams)

	return propSpecFact
}

func (defStmt *DefExistPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefBody.DefHeader.Params {
		// propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
		propSpecFactParams = append(propSpecFactParams, FcAtom(param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom(defStmt.DefBody.DefHeader.Name), propSpecFactParams)

	return propSpecFact
}

func (stmt *SpecFactStmt) ReverseParameterOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams), nil
}

func (stmt *SpecFactStmt) IsValidEqualFact() (bool, error) {
	if stmt.NameIs(glob.KeySymbolEqual) {
		if len(stmt.Params) == 2 {
			return true, nil
		} else {
			return false, fmt.Errorf("equal fact %s should have 2 params, but got %d", stmt.String(), len(stmt.Params))
		}
	} else {
		return false, nil
	}
}

func (stmt *SpecFactStmt) IsBuiltinProp_ExceptEqual() bool {
	// return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name) && !stmt.NameIs(glob.KeySymbolEqual)
	return glob.IsBuiltinInfixRelaPropSymbol(string(stmt.PropName)) && !stmt.NameIs(glob.KeySymbolEqual)
}

func (stmt *SpecFactStmt) IsMathInductionFact() bool {
	// return stmt.PropName.PkgName == glob.EmptyPkg && stmt.PropName.Name == glob.KeywordProveByMathInduction
	return string(stmt.PropName) == glob.KeywordProveByMathInduction
}

func NewInFact(param string, paramSet Fc) *SpecFactStmt {
	// return NewSpecFactStmt(TruePure, NewFcAtomWithName(glob.KeywordIn), []Fc{NewFcAtom(glob.EmptyPkg, param), paramSet})
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{FcAtom(param), paramSet})
}

func NewInFactWithFc(param Fc, paramSet Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom(glob.KeywordIn), []Fc{param, paramSet})
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

	return isFcAtomWithName(fcHeadAsFcFn.FnHead, glob.KeywordFn)
}

func isFcAtomWithName(fc Fc, name string) bool {
	fcAsFcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	// return fcAsFcAtom.Name == name && fcAsFcAtom.PkgName == glob.EmptyPkg
	return string(fcAsFcAtom) == name
}

func GetParamsSetFromInStatements(inStatements []FactStmt) ([]Fc, error) {
	paramsSets := []Fc{}
	for _, inStmt := range inStatements {
		paramSet, err := GetParamSetFromInStmt(inStmt)
		if err != nil {
			return nil, err
		}
		paramsSets = append(paramsSets, paramSet)
	}

	return paramsSets, nil
}

func GetParamSetFromInStmt(inStmt FactStmt) (Fc, error) {
	inStmtAsSpecFact, ok := inStmt.(*SpecFactStmt)
	if !ok {
		return nil, fmt.Errorf("GetParamsSetFromInStatements: expected SpecFactStmt, but got %T", inStmt)
	}
	if inStmtAsSpecFact.NameIs(glob.KeywordIn) {
		if len(inStmtAsSpecFact.Params) != 2 {
			return nil, fmt.Errorf("GetParamsSetFromInStatements: expected 2 params, but got %d", len(inStmtAsSpecFact.Params))
		}
		return inStmtAsSpecFact.Params[1], nil
	}

	return nil, fmt.Errorf("GetParamsSetFromInStatements: expected In fact, but got %s", inStmtAsSpecFact.String())
}

func (stmt *SpecFactStmt) ReverseSpecFactParamsOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("ReverseSpecFactParamsOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}
	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams), nil
}

func MakeFnSetFc(fnSets []Fc, retSet Fc) Fc {
	return NewFcFn(NewFcFn(FcAtom(glob.KeywordFn), fnSets), []Fc{retSet})
}

func (stmt *DefObjStmt) NewInFacts() []*SpecFactStmt {
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

func (stmt *SpecFactStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{stmt.PropName}
	for _, param := range stmt.Params {
		atoms = append(atoms, GetAtomsInFc(param)...)
	}
	return atoms
}

func (stmt *EnumStmt) GetAtoms() []FcAtom {
	atomsOfName := GetAtomsInFc(stmt.EnumName)

	atoms := []FcAtom{}
	atoms = append(atoms, atomsOfName...)
	for _, value := range stmt.EnumValues {
		atoms = append(atoms, GetAtomsInFc(value)...)
	}
	return atoms
}

func (stmt *UniFactStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{}
	for _, param := range stmt.ParamSets {
		atoms = append(atoms, GetAtomsInFc(param)...)
	}
	for _, fact := range stmt.DomFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	for _, fact := range stmt.ThenFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	// for _, fact := range stmt.IffFacts {
	// 	atoms = append(atoms, fact.GetAtoms()...)
	// }

	// 如果这个atom是param，那把这项扔了
	ret := []FcAtom{}
	for _, atom := range atoms {
		// if slices.Contains(stmt.Params, atom.Name) && atom.PkgName == glob.EmptyPkg {
		if slices.Contains(stmt.Params, string(atom)) {
			continue
		} else {
			ret = append(ret, atom)
		}
	}

	return ret
}

func (stmt *UniFactWithIffStmt) GetAtoms() []FcAtom {
	atoms := stmt.UniFact.GetAtoms()
	for _, fact := range stmt.IffFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *OrStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{}
	for _, fact := range stmt.Facts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func IsFnDeclarationFc(fc Fc) bool {
	fcAsFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	fcAsFnHeadAsFn, ok := fcAsFn.FnHead.(*FcFn)
	if !ok {
		return false
	}

	return isFcAtomWithName(fcAsFnHeadAsFn.FnHead, glob.KeywordFn)
}

func GetFnDeclarationFcInsideItems(fc Fc) ([]Fc, Fc) {
	fcAsFn, ok := fc.(*FcFn)
	if !ok {
		return nil, nil
	}

	fcAsFnHeadAsFn, ok := fcAsFn.FnHead.(*FcFn)
	if !ok {
		return nil, nil
	}

	paramSets := []Fc{}
	paramSets = append(paramSets, fcAsFnHeadAsFn.Params...)

	return paramSets, fcAsFn.Params[0]
}

func FromFnDeclFcToDefFnStmt(name string, fc Fc) *FnTemplateStmt {
	paramSets, retSet := GetFnDeclarationFcInsideItems(fc)

	params := []string{}

	for range len(paramSets) {
		randomStr := glob.RandomString(4)
		params = append(params, randomStr)
	}

	fnDefStmt := NewFnTemplateStmt(NewDefHeader(name, params, paramSets), []FactStmt{}, []FactStmt{}, retSet)

	return fnDefStmt
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

	if !isFcAtomWithName(fcAsFcFnHeadAsFcFn.FnHead, glob.KeywordFn) {
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

func GetExistFactExistParamsAndFactParams(stmt *SpecFactStmt) ([]Fc, []Fc) {
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

	return isFcAtomWithName(fcAsFcFnHeadAsFcFn.FnHead, name)
}

func IsFnFcFn(fc Fc) bool {
	return isFcWithFcFnHeadWithName(fc, glob.KeywordFn)
}

func FnFcToFnTemplateStmt(fc Fc) (*FnTemplateStmt, error) {
	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("expected FcFn, but got %T", fc)
	}

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

	fnDefStmt := NewFnTemplateStmt(NewDefHeader(glob.EmptyPkg, randomParams, paramSets), []FactStmt{}, []FactStmt{}, retSet)

	return fnDefStmt, nil
}

func IsFcAtomWithBuiltinPkgAndName(fc Fc, name string) bool {
	fcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	// return fcAtom.PkgName == glob.BuiltinPkgName && fcAtom.Name == name
	return string(fcAtom) == name
}

func (fcAtom FcAtom) WithoutPkgName() bool {
	// string has no colon colon
	return !strings.Contains(string(fcAtom), glob.KeySymbolColonColon)
}

func TransformEnumToUniFact(setName Fc, enumFcs []Fc) (*UniFactStmt, []*SpecFactStmt) {
	freeObjName := FcAtom(glob.RandomString(4))
	equalFacts := []*SpecFactStmt{}
	for _, fc := range enumFcs {
		equalFacts = append(equalFacts, NewSpecFactStmt(TruePure, FcAtom(glob.KeySymbolEqual), []Fc{freeObjName, fc}))
	}

	orFact := NewOrStmt(equalFacts)
	newUniFact := NewUniFact([]string{string(freeObjName)}, []Fc{setName}, []FactStmt{}, []FactStmt{orFact})

	return newUniFact, equalFacts
}
