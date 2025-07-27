// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) ver_In_FnTT(left ast.Fc, right *ast.FcFn, state VerState) (bool, error) {
	leftLatestFnT, ok := ver.env.GetLatestFnTT_GivenNameIsIn(left.String())
	if !ok {
		return false, nil
	}

	// right dom <= left dom. on right dom left has all those then facts
	rightDefT, ok := ver.env.GetFnTemplateDef_KeyIsFcHead(right)
	if !ok {
		return false, nil
	}

	ok = ver.leftFnTStructDom_Is_SubsetOf_RightFnTStructDom(leftLatestFnT.FnTemplateStmt, &rightDefT.Fn)

	if !ok {
		return false, nil
	}

	templateParamUniMap := map[string]ast.Fc{}
	for i, param := range rightDefT.TemplateDefHeader.Params {
		templateParamUniMap[param] = right.Params[i]
	}

	ok = ver.f_satisfy_FnT_ThenFacts_On_FnT_Dom(left, string(rightDefT.TemplateDefHeader.Name), templateParamUniMap, &rightDefT.Fn, state)
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) leftFnTStructDom_Is_SubsetOf_RightFnTStructDom(leftFnTStruct *ast.FnTStruct, rightFnTStruct *ast.FnTStruct) bool {
	return true
}

func (ver *Verifier) f_satisfy_FnT_ThenFacts_On_FnT_Dom(f ast.Fc, fnTDefName string, templateParamUniMap map[string]ast.Fc, fnT *ast.FnTStruct, state VerState) bool {
	derivedUniFact, err := fnT.DeriveUniFact(fnTDefName, f, templateParamUniMap)
	if err != nil {
		return false
	}

	ok, err := ver.VerFactStmt(derivedUniFact, state)
	if err != nil {
		return false
	}

	return ok
}
