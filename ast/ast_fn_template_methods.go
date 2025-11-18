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

import glob "golitex/glob"

func (fnTemplate *FnTStruct) DeriveUniFact_WithGivenFn(fc Obj) (*UniFactStmt, error) {
	paramAsFc := []Obj{}
	for _, param := range fnTemplate.Params {
		paramAsFc = append(paramAsFc, AtomObj(param))
	}

	thenFacts := []FactStmt{NewInFactWithParamFc(NewFcFn(fc, paramAsFc), fnTemplate.RetSet)}
	thenFacts = append(thenFacts, fnTemplate.ThenFacts...)

	notInstantiated := NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplate.DomFacts, thenFacts, fnTemplate.Line)

	return notInstantiated, nil
}

func (fnTemplate *FnTStruct) DeriveUniFact(defFnTemplateName string, fnFc Obj, templateParamUniMap map[string]Obj) (*UniFactStmt, error) {
	paramAsFc := []Obj{}
	for _, param := range fnTemplate.Params {
		paramAsFc = append(paramAsFc, AtomObj(param))
	}

	thenFacts := []FactStmt{NewInFactWithParamFc(NewFcFn(fnFc, paramAsFc), fnTemplate.RetSet)}
	thenFacts = append(thenFacts, fnTemplate.ThenFacts...)

	notInstantiated := NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplate.DomFacts, thenFacts, fnTemplate.Line)

	uniMap := glob.CopyMap(templateParamUniMap)
	uniMap[defFnTemplateName] = fnFc

	instantiated, err := notInstantiated.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return instantiated.(*UniFactStmt), nil
}

func (stmt *FnTStruct) InstantiateFnTWithoutChangingTName(uniMap map[string]Obj) ([]Obj, FactStmtSlice, FactStmtSlice, Obj, error) {
	// 1. instantiate set params in facts
	newSetParams := []Obj{}
	for _, setParam := range stmt.ParamSets {
		instantiatedParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, nil, nil, nil, err
		}
		newSetParams = append(newSetParams, instantiatedParam)
	}

	// 2. instantiate dom facts
	instantiatedDomFacts, err := stmt.DomFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	// 3. instantiate then facts
	instantiatedThenFacts, err := stmt.ThenFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	// 4. instantiate ret set
	instantiatedRetSet, err := stmt.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	return newSetParams, instantiatedDomFacts, instantiatedThenFacts, instantiatedRetSet, nil
}
