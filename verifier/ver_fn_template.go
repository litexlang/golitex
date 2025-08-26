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

import (
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) ver_In_FnTT(left ast.Fc, right *ast.FcFn, state *VerState) (bool, error) {
	leftLatestFnT, ok := ver.env.GetLatestFnT_GivenNameIsIn(left.String())
	if !ok {
		return false, nil
	}

	// right dom <= left dom. on right dom left has all those then facts
	rightDefT, ok := ver.env.GetFnTemplateDef_KeyIsFcHead(right)
	if !ok {
		return false, nil
	}

	ok = ver.leftFnTStructDom_Is_SubsetOf_RightFnTStructDom(leftLatestFnT, rightDefT, left, right, state)

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

// right dom is subset of left dom
func (ver *Verifier) leftFnTStructDom_Is_SubsetOf_RightFnTStructDom(leftFnTStruct *env.FnInFnTMemItem, rightFnTDef *ast.FnTemplateDefStmt, left ast.Fc, rightFn *ast.FcFn, state *VerState) bool {
	if len(rightFnTDef.TemplateDefHeader.Params) != len(rightFn.Params) {
		return false
	}

	instRightFnT, err := rightFnTDef.Fn.InstantiateFnStruct_FnName(string(rightFnTDef.TemplateDefHeader.Name), left)
	if err != nil {
		return false
	}

	instRightFnT, err = instRightFnT.Instantiate_FnTDefParams(rightFnTDef.TemplateDefHeader.Params, rightFn.Params)
	if err != nil {
		return false
	}

	mapLeftParamsToRightParams := map[string]ast.Fc{}
	for i, param := range leftFnTStruct.AsFnTStruct.Params {
		mapLeftParamsToRightParams[param] = ast.FcAtom(instRightFnT.Params[i])
	}

	leftDom, err := leftFnTStruct.AsFnTStruct.DomFacts.Instantiate(mapLeftParamsToRightParams)
	if err != nil {
		return false
	}

	// forall x in right dom, x in left dom
	uniParams := instRightFnT.Params
	uniParamSets := instRightFnT.ParamSets
	uniDom := instRightFnT.DomFacts
	uniThen := leftDom
	uniFact := ast.NewUniFact(uniParams, uniParamSets, uniDom, uniThen)

	ok, err := ver.VerFactStmt(uniFact, state)
	if err != nil {
		return false
	}
	return ok
}

// all right in left
func (ver *Verifier) f_satisfy_FnT_ThenFacts_On_FnT_Dom(f ast.Fc, fnTDefName string, templateParamUniMap map[string]ast.Fc, fnT *ast.FnTStruct, state *VerState) bool {
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
