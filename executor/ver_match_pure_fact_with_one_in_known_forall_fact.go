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

package litex_executor

import (
	ast "golitex/ast"
)

func (ver *Verifier) matchPureFactWithOneInKnownUniFactAndCheckMatchedObjectsSatisfyUniFactConditions(knownUniFact *ast.UniFactStmt, pureFactInKnownUniFact *ast.PureSpecificFactStmt, given *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	ok, uniMap := ver.matchObjectsWithFreeParamsWithInstObjectsInPureFact(knownUniFact.Params, pureFactInKnownUniFact.Params, given.Params)

	if !ok {
		return ast.NewEmptyUnknownVerRet()
	}

	for i, paramSet := range knownUniFact.ParamSets {
		instParamSet, err := paramSet.Instantiate(uniMap)
		if err != nil {
			return ast.NewEmptyUnknownVerRet()
		}
		inFact := ast.NewInFactWithObj(uniMap[knownUniFact.Params[i]], instParamSet)
		ret := ver.VerFactStmt(inFact, state)
		if ret.IsNotTrue() {
			return ast.NewEmptyUnknownVerRet()
		}
	}

	nextState := NewVerState(2, false, true)
	for _, domFact := range knownUniFact.DomFacts {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return ast.NewEmptyUnknownVerRet()
		}

		switch asInstDomFact := instDomFact.(type) {
		case ast.SpecificFactStmt:
			ret := ver.VerFactStmt(asInstDomFact, nextState)
			if ret.IsNotTrue() {
				return ast.NewEmptyUnknownVerRet()
			}
		case *ast.OrStmt:
			ret := ver.VerFactStmt(instDomFact, nextState)
			if ret.IsNotTrue() {
				return ast.NewEmptyUnknownVerRet()
			}
		default:
			return ast.NewEmptyUnknownVerRet()
		}

	}

	return ast.NewTrueVerRet(given, nil, knownUniFact.String())
}
