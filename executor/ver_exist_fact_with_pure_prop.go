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
	glob "golitex/glob"
)

func (ver *Verifier) ExistStFactWithPureProp_FreeExistsStFactMatchInstExistStFact(freeExistStFact *ast.SpecFactStmt, instExistStFactToBeMatched *ast.SpecFactStmt, verState *VerState) *glob.VerMsg {
	freeExistParams, freeParams, freeSpecFact := freeExistStFact.ExistStFactToPropNameExistParamsParamsAndTrueSpecFactAfterSt()
	toBeMatchedExistParams, toBeMatchedParams := instExistStFactToBeMatched.ExistStFactToPropNameExistParamsParams()

	if len(freeExistParams) != len(toBeMatchedExistParams) || len(freeParams) != len(toBeMatchedParams) {
		return nil
	}

	uniMap := map[string]ast.Obj{}
	for i, freeExistParam := range freeExistParams {
		uniMap[freeExistParam.String()] = toBeMatchedExistParams[i]
	}

	instFreeSpecFact, err := freeSpecFact.Instantiate(uniMap)
	if err != nil {
		return nil
	}

	// 证明 inst Free Spec Fact 的每一个 param 等于 right 的 对应的 param
	for i, instFreeSpecFactParam := range instFreeSpecFact.(*ast.SpecFactStmt).Params {
		verRet := ver.VerFactStmt(ast.NewEqualFact(instFreeSpecFactParam, instExistStFactToBeMatched.Params[i]), verState)
		if verRet.IsNotTrue() {
			return nil
		}
	}

	return glob.NewVerMsg(freeExistStFact.String(), instExistStFactToBeMatched.Line, []string{instExistStFactToBeMatched.String()})
}

func (ver *Verifier) ExistStFactWithPureProp_FreeExistStFactMatchInstExistStFacts(freeExistStFact *ast.SpecFactStmt, instExistStFactToBeMatched []ast.SpecFactStmt, state *VerState) *glob.VerMsg {
	for _, toMatch := range instExistStFactToBeMatched {
		ret := ver.ExistStFactWithPureProp_FreeExistsStFactMatchInstExistStFact(freeExistStFact, &toMatch, state)
		if ret != nil {
			return ret
		}
	}

	return nil
}
