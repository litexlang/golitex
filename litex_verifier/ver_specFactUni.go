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

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

func (ver *Verifier) specFactUni(knownFact *mem.StoredUniSpecFact, uniConMap map[string]ast.Fc, state VerState) (bool, error) {
	// 这里貌似不需要对整个uniFact实例化，只要实例化then
	insKnownUniFact, err := knownFact.UniFact.Instantiate(uniConMap)
	if err != nil {
		return false, err
	}
	insKnownUniFactAsUniFact, ok := insKnownUniFact.(*ast.ConUniFactStmt)
	if !ok {
		return false, fmt.Errorf("")
	}

	ok, err = ver.instUniFactDomFacts(insKnownUniFactAsUniFact, state)
	if err != nil {
		return false, err
	}

	return ok, nil
}

func (ver *Verifier) instUniFactDomFacts(insUniFact *ast.ConUniFactStmt, state VerState) (bool, error) {
	nextState := state.addRound()

	for _, fact := range insUniFact.DomFacts {
		ok, err := ver.FactStmt(fact, nextState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
