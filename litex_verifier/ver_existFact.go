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

	propDef, ok := ver.env.GetExistPropDef(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, fmt.Errorf("exist fact %s has no definition", stmt.String())
	}

	var err error = nil

	uniConMap := map[string]ast.Fc{}
	for i, param := range propDef.Def.DefHeader.Params {
		uniConMap[param] = stmt.Params[i]
	}

	params := []string{}
	params = append(params, propDef.ExistParams...)

	setParams := []ast.Fc{}
	setParams = append(setParams, propDef.ExistParamSets...)

	domFacts := []ast.FactStmt{}
	for _, fact := range propDef.Def.DomFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	specThenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range propDef.Def.IffFacts {
		fixed, err := thenFact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		fixedAsSpecFact, ok := fixed.(*ast.SpecFactStmt)
		if !ok {
			// 还是有可能then里不是 specFact的，比如定义可惜收敛；这时候我不报错，我只是让你不能证明 not exist。通常这种时候用法也都是 exist，用不着考虑not exist。你非要考虑not exist,那就用 not exist 来表示 forall，即给forall取个名字
			return false, nil
			// return false, fmt.Errorf("instantiate spec fact stmt failed")
		}
		fixedAsSpecFact = fixedAsSpecFact.ReverseSpecFact()
		specThenFacts = append(specThenFacts, fixedAsSpecFact)
	}

	thenFacts := []ast.FactStmt{}
	for _, fact := range specThenFacts {
		thenFacts = append(thenFacts, fact)
	}

	newUniFactUsingItself := ast.NewUniFactStmtWithSetReqInDom(params, setParams, domFacts, thenFacts, ast.EmptyIffFacts)

	ok, err = ver.FactStmt(newUniFactUsingItself, state)
	if err != nil {
		return false, err
	}
	if ok {
		return ver.factDefer(stmt, state, true, nil, newUniFactUsingItself.String())
	}

	return false, nil
}
