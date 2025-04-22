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
	ast "golitex/litex_ast"
)

func (ver *Verifier) ExistPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state.isSpec() {
		return false, nil
	}

	ok, err := ver.useExistPropDefProveExist(stmt, state, stmt.IsTrue())
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) useExistPropDefProveExist(stmt *ast.SpecFactStmt, state VerState, proveTrue bool) (bool, error) {
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
		fixedAsSpecFact := fixed.(*ast.SpecFactStmt)
		if proveTrue {
			fixedAsSpecFact = fixedAsSpecFact.ReverseIsTrue()
		}
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

// func (ver *Verifier) ExistPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
// 	if state.isSpec() {
// 		return false, nil
// 	}

// 	var newFact *ast.SpecFactStmt
// 	if stmt.TypeEnum == ast.TrueExist {
// 		// // 只要已经有一个是成立的，那整个exist就是成立的
// 		// if len(stmt.Params) != 0 {
// 		// }

// 		newFact = ast.NewSpecFactStmt(ast.TrueAtom, stmt.PropName, stmt.Params)

// 		ok, err := ver.SpecFact(newFact, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return ver.factDefer(stmt, state, true, nil, newFact.String())
// 		}
// 		return false, nil
// 	} else if stmt.TypeEnum == ast.FalseExist {
// 		// not exist 表示 forall，所以Litex的语法让涉及到的参数数量为0
// 		if len(stmt.Params) != 0 {
// 			return false, fmt.Errorf("exist fact with params is not supported %s", stmt.String())
// 		}

// 		propDef, ok := ver.env.PropMem.Get(stmt.PropName)
// 		if !ok {
// 			return false, nil
// 		}

// 		var err error = nil

// 		newUniFactUsingItself := ast.NewConUniFactStmt(propDef.DefHeader.Params, propDef.DefHeader.SetParams, propDef.DomFacts, []*ast.SpecFactStmt{ast.NewSpecFactStmt(ast.FalseAtom, stmt.PropName, []ast.Fc{})})
// 		for _, param := range propDef.DefHeader.Params {
// 			newUniFactUsingItself.ThenFacts[0].Params = append(newUniFactUsingItself.ThenFacts[0].Params, &ast.FcAtom{PkgName: glob.EmptyPkgName, PropName: param})
// 		}

// 		ok, err = ver.FactStmt(newUniFactUsingItself, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return ver.factDefer(stmt, state, true, nil, newUniFactUsingItself.String())
// 		}

// 		newUniFactUsingIff := ast.NewConUniFactStmt(propDef.DefHeader.Params, propDef.DefHeader.SetParams, propDef.DomFacts, []*ast.SpecFactStmt{})

// 		for _, fact := range propDef.IffFacts {
// 			newUniFactUsingIff.ThenFacts = append(newUniFactUsingIff.ThenFacts, fact.ReverseIsTrue())
// 		}

// 		ok, err = ver.FactStmt(newUniFactUsingIff, state)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return ver.factDefer(stmt, state, true, nil, newUniFactUsingIff.String())
// 		}

// 		return false, nil
// 	}

// 	return false, fmt.Errorf("invalid exist fact type: %d", stmt.TypeEnum)
// }
