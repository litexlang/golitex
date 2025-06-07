// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_ast

import (
	"errors"
)

func InstantiateFcAtom(fc *FcAtom, uniMap map[string]Fc) (Fc, error) {
	if fc.PkgName == "" {
		instance, ok := uniMap[fc.Name]
		if ok {
			return instance, nil
		}
	}
	return fc, nil
}

func (fc *FcAtom) Instantiate(uniMap map[string]Fc) (Fc, error) {
	return InstantiateFcAtom(fc, uniMap)
}

func InstantiateFcFn(fc *FcFn, uniMap map[string]Fc) (Fc, error) {
	var newFc FcFn

	newHead, err := fc.FnHead.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	if newHeadAsAtom, ok := newHead.(*FcAtom); ok {
		newFc.FnHead = newHeadAsAtom
	} else {
		newHeadAsFcFn, ok := newHead.(*FcFn)
		if !ok {
			return nil, errors.New("invalid type assertion for FnHead")
		}
		newFc.FnHead = newHeadAsFcFn.FnHead
		newFc.ParamSegs = append(newFc.ParamSegs, newHeadAsFcFn.ParamSegs...)
	}

	newParamSegs := make([]Fc, len(fc.ParamSegs))
	for i, seg := range fc.ParamSegs {
		newSeg, err := seg.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamSegs[i] = newSeg
	}
	newFc.ParamSegs = newParamSegs

	return &newFc, nil
}

func (fc *FcFn) Instantiate(uniMap map[string]Fc) (Fc, error) {
	return InstantiateFcFn(fc, uniMap)
}

func InstantiateSpecFact(stmt *SpecFactStmt, uniMap map[string]Fc) (*SpecFactStmt, error) {
	// 把 PropName 也换了
	newPropName, err := stmt.PropName.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	propNameAtom, ok := newPropName.(*FcAtom)
	if !ok {
		return nil, errors.New("PropName is not of type *FcAtom")
	}

	newParams := []Fc{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}

	return NewSpecFactStmt(stmt.TypeEnum, *propNameAtom, newParams), nil
}

func (stmt *SpecFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	return InstantiateSpecFact(stmt, uniMap)
}

func InstantiateUniFact(stmt *UniFactStmt, uniMap map[string]Fc) (*UniFactStmt, error) {
	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	newSetParams := []Fc{}
	for _, setParam := range stmt.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newSetParams = append(newSetParams, newSetParam)
	}

	// newParamInSetsFacts := ParamsParamSetsToInFacts(stmt.Params, newParamTypes)
	return NewUniFact(stmt.Params, newSetParams, newDomFacts, newThenFacts, newIffFacts), nil
}

func (stmt *UniFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	return InstantiateUniFact(stmt, uniMap)
}

func (defHeader *DefHeader) Instantiate(uniMap map[string]Fc) (*DefHeader, error) {
	newDefHeader := NewDefHeader(defHeader.Name, defHeader.Params, make([]Fc, len(defHeader.SetParams)))

	for i, setParam := range defHeader.SetParams {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDefHeader.SetParams[i] = newSetParam
	}

	return newDefHeader, nil
}

func (defPropStmt *DefPropStmt) Instantiate(uniMap map[string]Fc) (*DefPropStmt, error) {
	newDefHeader, err := defPropStmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newDomFacts := []FactStmt{}
	for _, fact := range defPropStmt.DomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range defPropStmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	return NewDefPropStmt(*newDefHeader, newDomFacts, newIffFacts), nil
}

func (stmt *DefExistPropStmtBody) Instantiate(uniMap map[string]Fc) (*DefExistPropStmtBody, error) {
	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newIffFacts := []LogicOrSpec_Stmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact.(LogicOrSpec_Stmt))
	}

	return NewDefExistPropBodyStmt(*newDefHeader, newDomFacts, newIffFacts), nil
}

func (stmt *DefExistPropStmt) Instantiate(uniMap map[string]Fc) (*DefExistPropStmt, error) {
	newDefExistPropBody, err := stmt.DefBody.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newExistParamSets := []Fc{}
	for _, setParam := range stmt.ExistParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newExistParamSets = append(newExistParamSets, newSetParam)
	}

	return NewDefExistPropStmt(newDefExistPropBody, stmt.ExistParams, newExistParamSets), nil
}

func (stmt *DefExistPropStmt) ExistParamInSetsFacts() []FactStmt {
	facts := []FactStmt{}
	for i, param := range stmt.ExistParams {
		facts = append(facts, NewInFact(param, stmt.ExistParamSets[i]))
	}
	return facts
}

func (stmt *OrStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	newOrFacts := make([]SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newFactPtr := newFact.(*SpecFactStmt)
		newOrFacts[i] = *newFactPtr
	}

	return NewOrStmt(newOrFacts), nil
}
