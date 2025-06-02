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
	"fmt"
	glob "golitex/glob"
	"strings"
)

type NameDepthMap map[string]int

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams NameDepthMap) (*FcAtom, error) {
	if atom == nil {
		return nil, nil
	}

	if prefixNum, ok := fcAtomInUniParams(atom, uniParams); ok {
		atom.Name = strings.Repeat(glob.UniParamPrefix, prefixNum) + atom.Name
	}

	return atom, nil
}

func AddUniPrefixToFc(fc Fc, uniParams NameDepthMap) (Fc, error) {

	if fc == nil {
		return nil, nil
	}

	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		return AddUniPrefixToFcAtom(fcAsAtom, uniParams)
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}
	var newFc FcFn

	var err error = nil

	newFc.FnHead, err = AddUniPrefixToFc(fcAsFcFn.FnHead, uniParams)
	if err != nil {
		return nil, err
	}

	for _, seg := range fcAsFcFn.ParamSegs {
		newSeg, err := AddUniPrefixToFc(seg, uniParams)
		if err != nil {
			return nil, err
		}
		newFc.ParamSegs = append(newFc.ParamSegs, newSeg)
	}

	return &newFc, nil
}

func fcAtomInUniParams(atom *FcAtom, uniParams NameDepthMap) (int, bool) {
	if atom.PkgName == glob.EmptyPkg {
		if prefixNum, ok := uniParams[atom.Name]; ok {
			return prefixNum, true
		}
	}
	return 0, false
}

func AddUniPrefixToUniFact(asUniFact *UniFactStmt) (*UniFactStmt, error) {
	uniMap := map[string]Fc{}
	newParams := make([]string, len(asUniFact.Params))

	for i, param := range asUniFact.Params {
		newParams[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, param)
		uniMap[param] = NewFcAtom(glob.EmptyPkg, newParams[i])
	}

	newDomFacts := []FactStmt{}
	newThenFacts := []FactStmt{}
	newIffFacts := EmptyIffFacts

	for _, fact := range asUniFact.DomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	for _, fact := range asUniFact.ThenFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}

	newSetParams := []Fc{}
	for _, setParam := range asUniFact.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newSetParams = append(newSetParams, newSetParam)
	}

	newParamInSetsFacts := []FactStmt{}
	for _, inSetFact := range asUniFact.ParamInSetsFacts {
		newFact, err := inSetFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamInSetsFacts = append(newParamInSetsFacts, newFact)
	}

	newUniFact := newUniFactStmt(newParams, newSetParams, newDomFacts, newThenFacts, newIffFacts, newParamInSetsFacts)

	return newUniFact, nil
}
