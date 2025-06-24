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

func (stmt *FnTemplateStmt) InstantiateByFnName_WithTemplateNameGivenFc(fc Fc) (*FnTemplateStmt, error) {
	newParamSets, newDomFacts, newThenFacts, newRetSet, err := stmt.InstantiateFnTWithoutChangingTName(map[string]Fc{stmt.Name: fc})
	if err != nil {
		return nil, err
	}

	return NewFnTemplateStmt(*NewDefHeader(fc.String(), stmt.Params, newParamSets), newDomFacts, newThenFacts, newRetSet), nil
}

func (fnTemplate *FnTemplateStmt) DeriveUniFact(fn Fc) *UniFactStmt {
	// return NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplate.DomFacts, append(fnTemplate.ThenFacts, NewSpecFactStmt(TruePure, NewFcAtomWithName(glob.KeywordIn), []Fc{fn, fnTemplate.RetSet})))
	return NewUniFact(fnTemplate.Params, fnTemplate.ParamSets, fnTemplate.DomFacts, fnTemplate.ThenFacts)
}

func (stmt *FnTemplateStmt) InstantiateFnTWithoutChangingTName(uniMap map[string]Fc) ([]Fc, FactStmtSlice, FactStmtSlice, Fc, error) {
	// 1. instantiate set params in facts
	newSetParams := []Fc{}
	for _, setParam := range stmt.ParamSets {
		instantiatedParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, nil, nil, nil, err
		}
		newSetParams = append(newSetParams, instantiatedParam)
	}

	// 2. instantiate dom facts
	instantiatedDomFacts, err := stmt.DomFacts.Instantiate(uniMap)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	// 3. instantiate then facts
	instantiatedThenFacts, err := stmt.ThenFacts.Instantiate(uniMap)
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
