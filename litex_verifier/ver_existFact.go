// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
)

func (ver *Verifier) ExistPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state.isSpec() {
		return false, nil
	}

	if stmt.TypeEnum == ast.TrueExist {
		newFact := ast.NewSpecFactStmt(ast.TrueAtom, stmt.PropName, stmt.Params)

		ok, err := ver.SpecFact(newFact, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newFact.String())
		}
		return false, nil

	} else if stmt.TypeEnum == ast.FalseExist {
		// get the definition of the prop

		propDef, ok := ver.env.PropMem.Get(stmt.PropName)
		if !ok {
			return false, fmt.Errorf("property %s not found", stmt.PropName)
		}

		newUniFact := ast.NewConUniFactStmt(propDef.DefHeader.Params, propDef.DefHeader.SetParams, propDef.DomFacts, []*ast.SpecFactStmt{})

		for _, fact := range propDef.IffFacts {
			newUniFact.ThenFacts = append(newUniFact.ThenFacts, fact.ReverseIsTrue())
		}

		ok, err := ver.FactStmt(newUniFact, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newUniFact.String())
		}

		return false, nil
	}

	return false, nil
}
