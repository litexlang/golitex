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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
)

func (stmt *SpecFactStmt) IsBuiltinInfixRelaProp() bool {
	return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name)
}

func (stmt *UniFactStmt) NewUniFactWithThenToIff() *UniFactStmt {
	newUniFact := NewUniFact(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.IffFacts, EmptyIffFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.ThenFacts...)
	return newUniFact
}

func (stmt *UniFactStmt) NewUniFactWithIffToThen() *UniFactStmt {
	newUniFact := NewUniFact(stmt.Params, stmt.ParamSets, stmt.DomFacts, stmt.ThenFacts, EmptyIffFacts)
	newUniFact.DomFacts = append(newUniFact.DomFacts, stmt.IffFacts...)
	return newUniFact
}

func MergeOuterInnerUniFacts(outer *UniFactStmt, inner *UniFactStmt) *UniFactStmt {
	newOuter := NewUniFact(outer.Params, outer.ParamSets, outer.DomFacts, inner.ThenFacts, EmptyIffFacts)

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

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, defStmt.DefHeader.Name}, propSpecFactParams)

	// prop to iff
	propToIffDomFacts := []FactStmt{propSpecFact}
	propToIffDomFacts = append(propToIffDomFacts, defStmt.DomFacts...)

	propToIff := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, propToIffDomFacts, defStmt.IffFacts, EmptyIffFacts)

	// iff to prop
	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return propToIff, IffToProp, nil
}

func (defStmt *DefPropStmt) IffToPropUniFact() *UniFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, defStmt.DefHeader.Name}, propSpecFactParams)

	IffToPropDomFacts := []FactStmt{}
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.DomFacts...)
	IffToPropDomFacts = append(IffToPropDomFacts, defStmt.IffFacts...)

	IffToProp := NewUniFact(defStmt.DefHeader.Params, defStmt.DefHeader.SetParams, IffToPropDomFacts, []FactStmt{propSpecFact}, EmptyIffFacts)

	return IffToProp
}

func (defStmt *DefPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, defStmt.DefHeader.Name}, propSpecFactParams)

	return propSpecFact
}

func (defStmt *DefExistPropStmt) ToSpecFact() *SpecFactStmt {
	propSpecFactParams := []Fc{}
	for _, param := range defStmt.DefBody.DefHeader.Params {
		propSpecFactParams = append(propSpecFactParams, NewFcAtom(glob.EmptyPkg, param))
	}

	propSpecFact := NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, defStmt.DefBody.DefHeader.Name}, propSpecFactParams)

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
	return stmt.PropName.PkgName == glob.EmptyPkg && glob.IsBuiltinInfixRelaPropSymbol(stmt.PropName.Name) && !stmt.NameIs(glob.KeySymbolEqual)
}

func (stmt *SpecFactStmt) IsMathInductionFact() bool {
	return stmt.PropName.PkgName == glob.EmptyPkg && stmt.PropName.Name == glob.KeywordProveByMathInduction
}

func NewInFact(param string, paramSet Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, glob.KeywordIn}, []Fc{NewFcAtom(glob.EmptyPkg, param), paramSet})
}

func NewInFactWithFc(param Fc, paramSet Fc) *SpecFactStmt {
	return NewSpecFactStmt(TruePure, FcAtom{glob.EmptyPkg, glob.KeywordIn}, []Fc{param, paramSet})
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
	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams), nil
}

func MakeFnSetFc(fnSets []Fc, retSet Fc) Fc {
	return NewFcFn(NewFcFn(NewFcAtomWithName(glob.KeywordFn), fnSets), []Fc{retSet})
}

func (stmt *DefObjStmt) NewInFacts() []*SpecFactStmt {
	facts := []*SpecFactStmt{}
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
