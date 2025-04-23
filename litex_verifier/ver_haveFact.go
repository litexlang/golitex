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

func (ver *Verifier) HavePropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	if state.isSpec() {
		return false, nil
	}

	ok, err := ver.useExistPropDefProveHave(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func (ver *Verifier) useExistPropDefProveHave(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	propDef, ok := ver.env.GetExistPropDef(stmt.PropName)
	if !ok {
		// TODO: 如果没声明，应该报错
		return false, nil
	}

	sepIndex := stmt.HaveSeparatorIndex()
	if sepIndex == -1 {
		return false, fmt.Errorf("have fact %s has no separator", stmt.String())
	}

	uniConMap := map[string]ast.Fc{}
	for i := 0; i < sepIndex; i++ {
		uniConMap[propDef.ExistParams[i]] = stmt.Params[i]
	}

	for i := sepIndex + 1; i < len(stmt.Params); i++ {
		uniConMap[propDef.Def.DefHeader.Params[i-sepIndex-1]] = stmt.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, fact := range propDef.Def.DomFacts {
		fixed, err := fact.Instantiate(uniConMap)
		if err != nil {
			return false, err
		}
		domFacts = append(domFacts, fixed)
	}

	thenFacts := []*ast.SpecFactStmt{}
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
		if !stmt.IsTrue() {
			fixedAsSpecFact = fixedAsSpecFact.ReverseIsTrue()
		}
		thenFacts = append(thenFacts, fixedAsSpecFact)
	}

	for _, domFact := range domFacts {
		ok, err := ver.FactStmt(domFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				msg := fmt.Sprintf("dom fact %s is unkown\n", domFact.String())
				ver.unknownMsgEnd(msg)
			}
			return false, nil
		}
	}

	for _, thenFact := range thenFacts {
		ok, err := ver.FactStmt(thenFact, state)
		if err != nil {
			return false, err
		}
		if ok {
			return ver.factDefer(stmt, state, true, nil, thenFact.String())
		}
	}

	return false, nil
}
