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
	"maps"
)

func (fnTemplate *AnonymousFn) DeriveUniFact_WithGivenFn(obj Obj) (*UniFactStmt, error) {
	paramAsObj := []Obj{}
	for _, param := range fnTemplate.Params {
		paramAsObj = append(paramAsObj, Atom(param))
	}

	thenFacts := []Spec_OrFact{NewInFactWithParamObj(NewFnObj(obj, paramAsObj), fnTemplate.RetSet, fnTemplate.Line)}

	thenFactsReversible := []Spec_OrFact{}
	for _, thenFact := range fnTemplate.ThenFacts {
		if specFact, ok := thenFact.(SpecificFactStmt); ok {
			thenFactsReversible = append(thenFactsReversible, specFact)
		} else if orStmt, ok := thenFact.(*OrStmt); ok {
			thenFactsReversible = append(thenFactsReversible, orStmt)
		} else {
			return nil, fmt.Errorf("then fact is not SpecificFactStmt or OrStmt")
		}
	}

	thenFacts = append(thenFacts, thenFactsReversible...)

	fnTemplateDomFacts := []Spec_OrFact{}
	for _, domFact := range fnTemplate.DomFacts {
		if specFact, ok := domFact.(SpecificFactStmt); ok {
			fnTemplateDomFacts = append(fnTemplateDomFacts, specFact)
		} else if orStmt, ok := domFact.(*OrStmt); ok {
			fnTemplateDomFacts = append(fnTemplateDomFacts, orStmt)
		} else {
			return nil, fmt.Errorf("dom fact is not SpecificFactStmt or OrStmt")
		}
	}

	notInstantiated := NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplateDomFacts, thenFacts, fnTemplate.Line)

	return notInstantiated, nil
}

func (fnTemplate *AnonymousFn) DeriveUniFact(defFnTemplateName string, fnObj Obj, templateParamUniMap map[string]Obj) (*UniFactStmt, error) {
	paramAsObj := []Obj{}
	for _, param := range fnTemplate.Params {
		paramAsObj = append(paramAsObj, Atom(param))
	}

	thenFacts := []Spec_OrFact{NewInFactWithParamObj(NewFnObj(fnObj, paramAsObj), fnTemplate.RetSet, fnTemplate.Line)}

	thenFactsReversible := []Spec_OrFact{}
	for _, thenFact := range fnTemplate.ThenFacts {
		if specFact, ok := thenFact.(SpecificFactStmt); ok {
			thenFactsReversible = append(thenFactsReversible, specFact)
		} else if orStmt, ok := thenFact.(*OrStmt); ok {
			thenFactsReversible = append(thenFactsReversible, orStmt)
		} else {
			return nil, fmt.Errorf("then fact is not SpecificFactStmt or OrStmt")
		}
	}

	thenFacts = append(thenFacts, thenFactsReversible...)

	fnTemplateDomFacts := []Spec_OrFact{}
	for _, domFact := range fnTemplate.DomFacts {
		if specFact, ok := domFact.(SpecificFactStmt); ok {
			fnTemplateDomFacts = append(fnTemplateDomFacts, specFact)
		} else if orStmt, ok := domFact.(*OrStmt); ok {
			fnTemplateDomFacts = append(fnTemplateDomFacts, orStmt)
		} else {
			return nil, fmt.Errorf("dom fact is not SpecificFactStmt or OrStmt")
		}
	}

	notInstantiated := NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplateDomFacts, thenFacts, fnTemplate.Line)

	uniMap := maps.Clone(templateParamUniMap)
	uniMap[defFnTemplateName] = fnObj

	instantiated, err := notInstantiated.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return instantiated.(*UniFactStmt), nil
}

func (stmt *AnonymousFn) InstantiateFnTWithoutChangingTName(uniMap map[string]Obj) ([]Obj, ReversibleFacts, ReversibleFacts, Obj, error) {
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
