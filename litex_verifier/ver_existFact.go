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

	ok, err := ver.useExistPropDefProveExist(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) useExistPropDefProveExist(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if stmt.IsTrue() {
		return false, nil
	}

	propDef, ok := ver.env.ExistPropMem.Get(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, nil
	}

	var err error = nil

	freeFixmap := map[string]ast.Fc{}
	for i, param := range propDef.Def.DefHeader.Params {
		freeFixmap[param] = stmt.Params[i]
	}

	params := []string{}
	params = append(params, propDef.ExistParams...)

	setParams := []ast.Fc{}
	setParams = append(setParams, propDef.ExistParamSets...)

	domFacts := []ast.FactStmt{}
	for _, fact := range propDef.Def.DomFacts {
		fixed, err := fact.Instantiate(freeFixmap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	thenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range propDef.Def.IffFacts {
		fixed, err := thenFact.Instantiate(freeFixmap)
		if err != nil {
			return false, err
		}
		fixedAsSpecFact, ok := fixed.(*ast.SpecFactStmt)
		if !ok {
			return false, fmt.Errorf("instantiate spec fact stmt failed")
		}
		fixedAsSpecFact = fixedAsSpecFact.ReverseIsTrue()
		thenFacts = append(thenFacts, fixedAsSpecFact)
	}

	newUniFactUsingItself := ast.NewConUniFactStmt(params, setParams, domFacts, thenFacts)

	ok, err = ver.FactStmt(newUniFactUsingItself, state)
	if err != nil {
		return false, err
	}
	if ok {
		return ver.factDefer(stmt, state, true, nil, newUniFactUsingItself.String())
	}

	return false, nil
}
