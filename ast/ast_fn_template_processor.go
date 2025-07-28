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

import "fmt"

func (stmt *FnTStruct) Instantiate(uniMap map[string]Fc) (*FnTStruct, error) {
	var err error

	newParamSets := make(FcSlice, len(stmt.ParamSets))
	for i := 0; i < len(stmt.ParamSets); i++ {
		newParamSets[i], err = stmt.ParamSets[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
	}

	newDomFacts := make(FactStmtSlice, len(stmt.DomFacts))
	for i := 0; i < len(stmt.DomFacts); i++ {
		newDomFacts[i], err = stmt.DomFacts[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
	}

	newThenFacts := make(FactStmtSlice, len(stmt.ThenFacts))
	for i := 0; i < len(stmt.ThenFacts); i++ {
		newThenFacts[i], err = stmt.ThenFacts[i].Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
	}

	newRetSet, err := stmt.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	return NewFnTStruct(stmt.Params, newParamSets, newRetSet, newDomFacts, newThenFacts), nil
}

func (stmt *FnTStruct) Instantiate_FnTDefParams(templateParams []string, params []Fc) (*FnTStruct, error) {
	if len(params) != len(templateParams) {
		return nil, fmt.Errorf("params length mismatch")
	}

	uniMap := map[string]Fc{}
	for i := 0; i < len(templateParams); i++ {
		uniMap[templateParams[i]] = params[i]
	}

	return stmt.Instantiate(uniMap)
}

func (stmt *FnTStruct) InstantiateFnStruct_FnName(fnTName string, fc Fc) (*FnTStruct, error) {
	uniMap := map[string]Fc{fnTName: fc}
	return stmt.Instantiate(uniMap)
}
