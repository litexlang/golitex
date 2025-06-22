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

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name)
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
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, NewFcAtomWithName(defStmt.DefHeader.Name), propSpecFactParams)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, propToIffDomFacts, defStmt.IffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact})

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, NewFcAtomWithName(defStmt.DefHeader.Name), propSpecFactParams)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact})

	return IffToProp
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, NewFcAtomWithName(defStmt.DefHeader.Name), propSpecFactParams)

	return propSpecFact
}

func (defStmt *DefExistPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefBody.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, NewFcAtomWithName(defStmt.DefBody.DefHeader.Name), propSpecFactParams)

	return propSpecFact
}

func (stmt *SpecFactStmt) ReverseParameterOrder() (*SpecFactStmt, error) {
	if len(stmt.Params) != 2 {
		return nil, fmt.Errorf("reverseParameterOrder: expected 2 params, but got %d", len(stmt.Params))
	}

	newParams := []Fc{stmt.Params[1], stmt.Params[0]}

	return NewSpecFactStmt(stmt.TypeEnum, &stmt.PropName, newParams), nil
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
	return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name) && !stmt.NameIs(glob.KeySymbolEqual)
}

func (stmt *SpecFactStmt) IsMathInductionFact() bool {
	return stmt.PropName.PkgName == glob.EmptyPkg && stmt.PropName.Name == glob.KeywordProveByMathInduction
}

func NewInFact(param string, paramSet Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, NewFcAtomWithName(glob.KeywordIn), []Fc{NewFcAtom(glob.EmptyPkg, param), paramSet})
}

func NewInFactWithFc(param Fc, paramSet Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, NewFcAtomWithName(glob.KeywordIn), []Fc{param, paramSet})
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
	fcAsFcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}

	return fcAsFcAtom.Name == name && fcAsFcAtom.PkgName == glob.EmptyPkg
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
	return NewSpecFactStmt(stmt.TypeEnum, &stmt.PropName, newParams), nil
}

func MakeFnSetFc(fnSets []Fc, retSet Fc) Fc {
	return NewFcFn(NewFcFn(NewFcAtomWithName(glob.KeywordFn), fnSets), []Fc{retSet})
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
		facts = append(facts, NewInFact(param, defHeader.SetParams[i]))
	}

	return facts
}

func (stmt *SpecFactStmt) GetAtoms() []*FcAtom {
	atoms := []*FcAtom{&stmt.PropName}
	for _, param := range stmt.Params {
		atoms = append(atoms, GetAtomsInFc(param)...)
	}
	return atoms
}

func (stmt *UniFactStmt) GetAtoms() []*FcAtom {
	atoms := []*FcAtom{}
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
	ret := []*FcAtom{}
	for _, atom := range atoms {
		if slices.Contains(stmt.Params, atom.Name) && atom.PkgName == glob.EmptyPkg {
			continue
		} else {
			ret = append(ret, atom)
		}
	}

	return ret
}

func (stmt *UniFactWithIffStmt) GetAtoms() []*FcAtom {
	atoms := stmt.UniFact.GetAtoms()
	for _, fact := range stmt.IffFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *OrStmt) GetAtoms() []*FcAtom {
	atoms := []*FcAtom{}
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

func FromFnDeclFcToDefFnStmt(name string, fc Fc) *DefFnStmt {
	paramSets, retSet := GetFnDeclarationFcInsideItems(fc)

	params := []string{}

	for range len(paramSets) {
		randomStr := glob.RandomString(4)
		params = append(params, randomStr)
	}

	fnDefStmt := NewDefFnStmt(*NewDefHeader(name, params, paramSets), []FactStmt{}, []FactStmt{}, retSet)

	return fnDefStmt
}

func Get_FnTemplate_InFcForm_ParamSetsAndRetSet(fc Fc) ([]Fc, Fc, error) {
	// given fc must be a function
	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, nil, fmt.Errorf("GetFnFcFnParamSetsAndRetSet: given fc is not a function")
	}

	fcAsFcFnHeadAsFcFn, ok := fcAsFcFn.FnHead.(*FcFn)
	if !ok {
		return nil, nil, fmt.Errorf("GetFnFcFnParamSetsAndRetSet: given fc is not a function")
	}

	// must have name fn
	if !isFcAtomWithName(fcAsFcFnHeadAsFcFn.FnHead, glob.KeywordFn) {
		return nil, nil, fmt.Errorf("GetFnFcFnParamSetsAndRetSet: given fc is not a function")
	}

	paramSets := []Fc{}
	paramSets = append(paramSets, fcAsFcFnHeadAsFcFn.Params...)

	return paramSets, fcAsFcFn.Params[0], nil
}
