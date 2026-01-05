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

func (ver *Verifier) ExistStFactWithPureProp_FreeExistsStFactMatchInstExistStFact(stmt *ast.HaveObjStStmt, freeExistStFact *ast.SpecFactStmt, instExistStFactToBeMatched *ast.SpecFactStmt, verState *VerState) *glob.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	freeExistParams, freeParams, freeSpecFact := freeExistStFact.ExistStFactToPropNameExistParamsParamsAndTrueSpecFactAfterSt()
	toBeMatchedExistParams, toBeMatchedParams := instExistStFactToBeMatched.ExistStFactToPropNameExistParamsParams()

	if len(freeExistParams) != len(toBeMatchedExistParams) || len(freeParams) != len(toBeMatchedParams) {
		return glob.NewEmptyVerRetUnknown()
	}

	uniMap := map[string]ast.Obj{}
	for i, freeExistParam := range freeExistParams {
		uniMap[freeExistParam.String()] = toBeMatchedExistParams[i]
	}

	instFreeSpecFact, err := freeSpecFact.Instantiate(uniMap)
	if err != nil {
		return glob.NewEmptyVerRetUnknown()
	}

	// 证明 inst Free Spec Fact 的每一个 param 等于 right 的 对应的 param
	for i, instFreeSpecFactParam := range instFreeSpecFact.(*ast.SpecFactStmt).Params {
		verRet := ver.VerFactStmt(ast.NewEqualFact(instFreeSpecFactParam, instExistStFactToBeMatched.Params[i]), verState)
		if verRet.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	// 证明 have 对应的 每一个 set ，对应的 exist_param 都在
	newUniMap := map[string]ast.Obj{}
	for i, paramSet := range stmt.ObjSets {
		instParamSet, err := paramSet.Instantiate(newUniMap)
		if err != nil {
			return glob.NewEmptyVerRetUnknown()
		}

		inFact := ast.NewInFactWithObj(instExistStFactToBeMatched.Params[i], instParamSet)

		ret := ver.VerFactStmt(inFact, verState)
		if ret.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}

		newUniMap[stmt.ObjNames[i]] = instExistStFactToBeMatched.Params[i]
	}

	return glob.NewVerMsg2(glob.StmtRetTypeTrue, freeExistStFact.String(), instExistStFactToBeMatched.Line, []string{instExistStFactToBeMatched.String()})
}

func (ver *Verifier) ExistStFactWithPureProp_FreeExistStFactMatchInstExistStFacts(stmt *ast.HaveObjStStmt, freeExistStFact *ast.SpecFactStmt, instExistStFactToBeMatched []ast.SpecFactStmt, state *VerState) *glob.VerRet {
	for _, curToMatch := range instExistStFactToBeMatched {
		ret := ver.ExistStFactWithPureProp_FreeExistsStFactMatchInstExistStFact(stmt, freeExistStFact, &curToMatch, state)
		if ret.IsTrue() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}
