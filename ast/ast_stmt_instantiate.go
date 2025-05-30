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

	// newParamInSetsFacts := ParamsParamSetsToInFacts(stmt.Params, newParamTypes)
	newParamInSetsFacts := make([]FactStmt, len(stmt.ParamInSetsFacts))
	for i, fact := range stmt.ParamInSetsFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamInSetsFacts[i] = newFact
	}

	return newUniFactStmt(stmt.Params, newDomFacts, newThenFacts, newIffFacts, newParamInSetsFacts), nil
}

func (stmt *UniFactStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
	return InstantiateUniFact(stmt, uniMap)
}

// func InstantiateLogicExprStmt(stmt *LogicExprStmt, uniMap map[string]Fc) (*LogicExprStmt, error) {
// 	newOrAnd := NewOrAndFact(stmt.IsOr, []Reversable_LogicOrSpec_Stmt{})
// 	for _, fact := range stmt.Facts {
// 		newFact, err := fact.Instantiate(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		// make newFact a LogicExprOrSpecFactStmt
// 		newFactAsLogicExprOrSpecFactStmt, ok := newFact.(Reversable_LogicOrSpec_Stmt)
// 		if !ok {
// 			return nil, errors.New("newFact is not of type LogicExprOrSpecFactStmt")
// 		}
// 		newOrAnd.Facts = append(newOrAnd.Facts, newFactAsLogicExprOrSpecFactStmt)
// 	}

// 	return newOrAnd, nil
// }

// func (stmt *LogicExprStmt) Instantiate(uniMap map[string]Fc) (FactStmt, error) {
// 	return InstantiateLogicExprStmt(stmt, uniMap)
// }

func (defHeader *DefHeader) Instantiate(uniMap map[string]Fc) (*DefHeader, error) {
	newDefHeader := NewDefHeader(defHeader.Name, defHeader.Params, make([]FactStmt, len(defHeader.ParamInSetsFacts)))

	for i, inSetFact := range defHeader.ParamInSetsFacts {
		newSetParam, err := inSetFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDefHeader.ParamInSetsFacts[i] = newSetParam
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

	newIffFacts := []Reversable_LogicOrSpec_Stmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact.(Reversable_LogicOrSpec_Stmt))
	}

	return NewDefExistPropBodyStmt(*newDefHeader, newDomFacts, newIffFacts), nil
}

func (stmt *DefExistPropStmt) Instantiate(uniMap map[string]Fc) (*DefExistPropStmt, error) {
	newDefExistPropBody, err := stmt.DefBody.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newExistParamInSetsFacts := make([]FactStmt, len(stmt.ExistInSetsFacts))
	for i, fact := range stmt.ExistInSetsFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newExistParamInSetsFacts[i] = newFact
	}

	return NewDefExistPropStmt(newDefExistPropBody, stmt.ExistParams, newExistParamInSetsFacts), nil
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
