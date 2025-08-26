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
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) GetFnTemplateSliceTheFnIsIn(fnName ast.Fc) ([]env.FnInFnTTMemItem, bool) {
	fnInFnTTMenItemSlice, ok := ver.env.GetFnTemplateSliceTheFnIsInFromEnv(fnName.String())
	if ok {
		return fnInFnTTMenItemSlice, true
	}

	fnNameAsFcFn, ok := fnName.(*ast.FcFn)
	if !ok {
		return nil, false
	}

	switch fnNameAsFcFn.FnHead.(type) {
	case ast.FcAtom:
		return ver.fcHeadIsAtom_InferTOfFc(fnNameAsFcFn)
	case *ast.FcFn:
		return nil, false
	default:
		return nil, false
	}
}

func (ver *Verifier) fcHeadIsAtom_InferTOfFc(fnNameAsFcFn *ast.FcFn) ([]env.FnInFnTTMemItem, bool) {
	head, ok := fnNameAsFcFn.FnHead.(ast.FcAtom)
	if !ok {
		return nil, false
	}

	fnInFnTTMemItem, ok := ver.env.GetLatestFnTT_GivenNameIsIn(head.String())
	if !ok {
		return nil, false
	}
	ret := env.MakeFnInFnTTMemItem(nil, nil)

	templateFnIsIn := env.MakeFnInFnTTMemItem(nil, nil)
	var err error
	if fnInFnTTMemItem.InFcFn != nil {
		uniMap := map[string]ast.Fc{}
		for i, param := range fnInFnTTMemItem.InFcFn.Params {
			uniMap[fnInFnTTMemItem.FnTemplateStmt.Params[i]] = param
		}

		InFcFn, err := fnInFnTTMemItem.InFcFn.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		templateFnIsIn.InFcFn = InFcFn.(*ast.FcFn)

		retFcFn, err := templateFnIsIn.InFcFn.Params[0].Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		retFcFnAsFcFn, ok := retFcFn.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		if ast.IsFnTemplate_FcFn(retFcFnAsFcFn) {
			ret.InFcFn = retFcFn.(*ast.FcFn)
		} else {
			// 不知道如何处理返回值是 template 的情况
			return nil, false
		}
	} else {
		uniMap := map[string]ast.Fc{}
		for i, param := range fnInFnTTMemItem.FnTemplateStmt.Params {
			uniMap[param] = fnNameAsFcFn.Params[i]
		}

		template, err := fnInFnTTMemItem.FnTemplateStmt.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		templateFnIsIn.FnTemplateStmt = template

		retTemplate, err := templateFnIsIn.FnTemplateStmt.RetSet.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		retTemplateFcFn, ok := retTemplate.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		if ast.IsFnTemplate_FcFn(retTemplateFcFn) {
			ret.InFcFn = retTemplateFcFn
		} else {
			// 不知道如何处理返回值是 template 的情况
			return nil, false
		}
	}

	// 参数满足 fnTemplateDef 的参数要求
	if templateFnIsIn.InFcFn != nil {
		ok, err = ver.paramsSatisfy_FcFnT_ParamsReq(fnNameAsFcFn, &templateFnIsIn)
	} else {
		ok, err = ver.paramsSatisfy_UserDefinedTemplate_ParamsReq(fnNameAsFcFn, &templateFnIsIn)
	}

	if err != nil {
		return nil, false
	}
	if !ok {
		return nil, false
	}

	// 代入到 retSet 里
	return []env.FnInFnTTMemItem{ret}, true
}

func (ver *Verifier) paramsSatisfy_FcFnT_ParamsReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTTMemItem) (bool, error) {
	head, ok := fnInFnTTMemItem.InFcFn.FnHead.(*ast.FcFn)
	if !ok {
		return false, nil
	}

	for i, setWhereParamIsIn := range head.Params {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(fcFn.Params[i], setWhereParamIsIn), Round0NoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil

}

func (ver *Verifier) paramsSatisfy_UserDefinedTemplate_ParamsReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTTMemItem) (bool, error) {
	if len(fcFn.Params) != len(fnInFnTTMemItem.FnTemplateStmt.Params) {
		return false, fmt.Errorf("parameters in %s must be %d, %s in %s is not valid", fcFn.FnHead, len(fnInFnTTMemItem.FnTemplateStmt.Params), fcFn, fcFn)
	}

	for i := range fcFn.Params {
		inFact := ast.NewInFactWithFc(fcFn.Params[i], fnInFnTTMemItem.FnTemplateStmt.ParamSets[i])
		ok, err := ver.VerFactStmt(inFact, Round0NoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, domFact := range fnInFnTTMemItem.FnTemplateStmt.DomFacts {
		ok, err := ver.VerFactStmt(domFact, Round0NoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
