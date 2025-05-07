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

import "errors"

func InstantiateFcAtom(fc *FcAtom, uniConMap map[string]Fc) (Fc, error) {
	if fc.PkgName == "" {
		instance, ok := uniConMap[fc.Name]
		if ok {
			return instance, nil
		}
	}
	return fc, nil
}

func (fc *FcAtom) Instantiate(uniConMap map[string]Fc) (Fc, error) {
	return InstantiateFcAtom(fc, uniConMap)
}

func InstantiateFcFn(fc *FcFn, uniConMap map[string]Fc) (Fc, error) {
	newFc := FcFn{&FcAtom{}, [][]Fc{}}

	newHead, err := fc.FnHead.Instantiate(uniConMap)
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

	for _, seg := range fc.ParamSegs {
		newSeg := []Fc{}
		for _, param := range seg {
			newParam, err := param.Instantiate(uniConMap)
			if err != nil {
				return nil, err
			}
			newSeg = append(newSeg, newParam)
		}
		newFc.ParamSegs = append(newFc.ParamSegs, newSeg)
	}

	return &newFc, nil
}

func (fc *FcFn) Instantiate(uniConMap map[string]Fc) (Fc, error) {
	return InstantiateFcFn(fc, uniConMap)
}

func InstantiateSpecFact(stmt *SpecFactStmt, uniConMap map[string]Fc) (*SpecFactStmt, error) {
	// 把 PropName 也换了
	newPropName, err := stmt.PropName.Instantiate(uniConMap)
	if err != nil {
		return nil, err
	}

	propNameAtom, ok := newPropName.(*FcAtom)
	if !ok {
		return nil, errors.New("PropName is not of type *FcAtom")
	}

	newParams := []Fc{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}

	return NewSpecFactStmt(stmt.TypeEnum, *propNameAtom, newParams), nil
}

func (stmt *SpecFactStmt) Instantiate(uniConMap map[string]Fc) (FactStmt, error) {
	return InstantiateSpecFact(stmt, uniConMap)
}

func InstantiateUniFact(stmt *UniFactStmt, uniConMap map[string]Fc) (*UniFactStmt, error) {
	newParamTypes := []Fc{}
	for _, param := range stmt.ParamSets {
		newParam, err := param.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newParamTypes = append(newParamTypes, newParam)
	}

	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		specFact, ok := newFact.(*SpecFactStmt)
		if !ok {
			return nil, errors.New("ThenFacts must be of type *SpecFactStmt")
		}
		newThenFacts = append(newThenFacts, specFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	return newConUniFactStmt(stmt.Params, newParamTypes, newDomFacts, newThenFacts, newIffFacts), nil
}

func (stmt *UniFactStmt) Instantiate(uniConMap map[string]Fc) (FactStmt, error) {
	return InstantiateUniFact(stmt, uniConMap)
}

func InstantiateLogicExprStmt(stmt *LogicExprStmt, uniConMap map[string]Fc) (*LogicExprStmt, error) {
	newOrAnd := NewOrAndFact(stmt.IsOr, []LogicExprOrSpecFactStmt{})
	for _, fact := range stmt.Facts {
		newFact, err := fact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		// make newFact a LogicExprOrSpecFactStmt
		newFactAsLogicExprOrSpecFactStmt, ok := newFact.(LogicExprOrSpecFactStmt)
		if !ok {
			return nil, errors.New("newFact is not of type LogicExprOrSpecFactStmt")
		}
		newOrAnd.Facts = append(newOrAnd.Facts, newFactAsLogicExprOrSpecFactStmt)
	}

	return newOrAnd, nil
}

func (stmt *LogicExprStmt) Instantiate(uniConMap map[string]Fc) (FactStmt, error) {
	return InstantiateLogicExprStmt(stmt, uniConMap)
}
