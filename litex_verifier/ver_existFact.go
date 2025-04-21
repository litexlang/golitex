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
	glob "golitex/litex_global"
)

func (ver *Verifier) ExistPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state.isSpec() {
		return false, nil
	}

	var newFact *ast.SpecFactStmt
	if stmt.TypeEnum == ast.TrueExist {
		newFact = ast.NewSpecFactStmt(ast.TrueAtom, stmt.PropName, stmt.Params)

		ok, err := ver.SpecFact(newFact, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newFact.String())
		}
		return false, nil
	} else if stmt.TypeEnum == ast.FalseExist {
		// not exist 表示 forall，所以Litex的语法让涉及到的参数数量为0
		if len(stmt.Params) != 0 {
			return false, fmt.Errorf("exist fact with params is not supported %s", stmt.String())
		}

		propDef, ok := ver.env.PropMem.Get(stmt.PropName)
		if !ok {
			return false, nil
		}

		newUniFactUsingIff := ast.NewConUniFactStmt(propDef.DefHeader.Params, propDef.DefHeader.SetParams, propDef.DomFacts, []*ast.SpecFactStmt{})

		for _, fact := range propDef.IffFacts {
			newUniFactUsingIff.ThenFacts = append(newUniFactUsingIff.ThenFacts, fact.ReverseIsTrue())
		}

		ok, err := ver.FactStmt(newUniFactUsingIff, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newUniFactUsingIff.String())
		}

		newUniFactUsingItself := ast.NewConUniFactStmt(propDef.DefHeader.Params, propDef.DefHeader.SetParams, propDef.DomFacts, []*ast.SpecFactStmt{ast.NewSpecFactStmt(ast.FalseAtom, stmt.PropName, []ast.Fc{})})
		for _, param := range propDef.DefHeader.Params {
			newUniFactUsingItself.ThenFacts[0].Params = append(newUniFactUsingItself.ThenFacts[0].Params, &ast.FcAtom{PkgName: glob.EmptyPkgName, PropName: param})
		}

		ok, err = ver.FactStmt(newUniFactUsingItself, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, newUniFactUsingItself.String())
		}

		return false, nil
	}

	return false, fmt.Errorf("invalid exist fact type: %d", stmt.TypeEnum)
}
