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

func InstantiateFcAtom(fc FcAtom, uniMap map[string]Fc) (Fc, error) {
	instance, ok := uniMap[string(fc)]
	if ok {
		return instance, nil
	}
	return fc, nil
}

func (fc FcAtom) Instantiate(uniMap map[string]Fc) (Fc, error) {
	return InstantiateFcAtom(fc, uniMap)
}

func InstantiateFcFn(fc *FcFn, uniMap map[string]Fc) (Fc, error) {
	newHead, err := fc.FnHead.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newParamSegs := make([]Fc, len(fc.Params))
	for i, seg := range fc.Params {
		newSeg, err := seg.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamSegs[i] = newSeg
	}

	return NewFcFn(newHead, newParamSegs), nil
}

func (fc *FcFn) Instantiate(uniMap map[string]Fc) (Fc, error) {
	return InstantiateFcFn(fc, uniMap)
}

func InstantiateSpecFact(stmt *SpecFactStmt, uniMap map[string]Fc) (*SpecFactStmt, error) {
	newParams := []Fc{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *SpecFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	return InstantiateSpecFact(stmt, uniMap)
}

func InstantiateUniFact(stmt *UniFactStmt, uniMap map[string]Fc) (*UniFactStmt, error) {
	newParams := []string{}
	newParams = append(newParams, stmt.Params...)

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

	newSetParams := []Fc{}
	for _, setParam := range stmt.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newSetParams = append(newSetParams, newSetParam)
	}

	return NewUniFact(newParams, newSetParams, newDomFacts, newThenFacts, stmt.Line), nil
}

func (stmt *UniFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	return InstantiateUniFact(stmt, uniMap)
}

func (defHeader *DefHeader) Instantiate(uniMap map[string]Fc) (*DefHeader, error) {
	newDefHeader := NewDefHeader(defHeader.Name, defHeader.Params, make([]Fc, len(defHeader.ParamSets)))

	for i, setParam := range defHeader.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDefHeader.ParamSets[i] = newSetParam
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

	newThenFacts := []FactStmt{}
	for _, fact := range defPropStmt.ThenFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}
	return NewDefPropStmt(newDefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line), nil
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

	newIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	return NewDefExistPropBodyStmt(newDefHeader, newDomFacts, newIffFacts, stmt.Line), nil
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

	return NewDefExistPropStmt(newDefExistPropBody, stmt.ExistParams, newExistParamSets, stmt.Line), nil
}

func (stmt *DefExistPropStmt) ExistParamInSetsFacts() []FactStmt {
	facts := []FactStmt{}
	for i, param := range stmt.ExistParams {
		facts = append(facts, NewInFact(param, stmt.ExistParamSets[i]))
	}
	return facts
}

func (stmt *OrStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	newOrFacts := make([]*SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newOrFacts[i] = newFact.(*SpecFactStmt)
	}

	return NewOrStmt(newOrFacts, stmt.Line), nil
}

func (stmt *UniFactWithIffStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	newUniFact, err := stmt.UniFact.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedIffFacts = append(instantiatedIffFacts, newFact)
	}

	return NewUniFactWithIff(newUniFact.(*UniFactStmt), instantiatedIffFacts, stmt.Line), nil
}

func (stmt *EnumStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	enumName, err := stmt.CurSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newEnumValues := []Fc{}
	for _, value := range stmt.Items {
		newValue, err := value.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newEnumValues = append(newEnumValues, newValue)
	}

	return NewEnumStmt(enumName, newEnumValues, stmt.Line), nil
}

func (stmt *IntensionalSetStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	newCurSet, err := stmt.CurSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newParentSet, err := stmt.ParentSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newProofs := make([]*SpecFactStmt, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		newProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProofs[i] = newProof.(*SpecFactStmt)
	}

	return NewIntensionalSetStmt(newCurSet, stmt.Param, newParentSet, newProofs, stmt.Line), nil
}

func (stmt *EqualsFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	newParams := []Fc{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}
	return NewEqualsFactStmt(newParams, stmt.Line), nil
}

func (fcSlice FcSlice) Instantiate(uniMap map[string]Fc) (FcSlice, error) {
	newFcSlice := make([]Fc, len(fcSlice))
	for i, fc := range fcSlice {
		newFc, err := fc.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newFcSlice[i] = newFc
	}
	return newFcSlice, nil
}

func (s SpecFactPtrSlice) Instantiate(uniMap map[string]Fc) (SpecFactPtrSlice, error) {
	newSpecFactPtrSlice := make([]*SpecFactStmt, len(s))
	for i, specFactPtr := range s {
		newSpecFactPtr, err := specFactPtr.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newSpecFactPtrSlice[i] = newSpecFactPtr.(*SpecFactStmt)
	}
	return newSpecFactPtrSlice, nil
}
