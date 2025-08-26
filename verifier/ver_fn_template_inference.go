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

func (ver *Verifier) GetFnTemplateSliceTheFnIsIn(fc ast.Fc) ([]env.FnInFnTMemItem, bool) {
	fnInFnTTMenItemSlice, ok := ver.env.GetFnTemplateSliceTheFnIsInFromEnv(fc.String())
	if ok {
		return fnInFnTTMenItemSlice, true
	}

	fcAsFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return nil, false
	}

	switch fcAsFcFn.FnHead.(type) {
	case ast.FcAtom:
		return ver.fcHeadIsAtom_InferTOfFc(fcAsFcFn)
	case *ast.FcFn:
		return nil, false
	default:
		return nil, false
	}
}

// fc = a(params)，其中 a(params)本身是一个函数，它在 fn(..) fn(..)ret 或 fn(..) T(..) 中
func (ver *Verifier) fcHeadIsAtom_InferTOfFc(fc *ast.FcFn) ([]env.FnInFnTMemItem, bool) {
	fcHeadAsAtom, ok := fc.FnHead.(ast.FcAtom)
	if !ok {
		return nil, false
	}

	fnInFnTMemItem, ok := ver.env.GetLatestFnT_GivenNameIsIn(fcHeadAsAtom.String())
	if !ok {
		return nil, false
	}

	var templateFcHeadIsIn *env.FnInFnTMemItem
	var templateFcIsIn *env.FnInFnTMemItem

	var err error
	if fnInFnTMemItem.InFcFn != nil {
		templateFcHeadIsIn, templateFcIsIn, ok = ver.FcHead_In_FcFnTWhoseRetIsAlsoT(fc, fnInFnTMemItem)
		if !ok {
			return nil, false
		}
	} else {
		// a(params) 中的a，在 T(): fn() T2() 或 T(): fn() fn()Ret 中

		uniMap := map[string]ast.Fc{}
		for i, param := range fnInFnTMemItem.FnTemplateStmt.Params {
			uniMap[param] = fc.Params[i]
		}

		template, err := fnInFnTMemItem.FnTemplateStmt.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		templateFcHeadIsIn.FnTemplateStmt = template

		retTemplate, err := templateFcHeadIsIn.FnTemplateStmt.RetSet.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		retTemplateFcFn, ok := retTemplate.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		if ast.IsFnTemplate_FcFn(retTemplateFcFn) {
			templateFcIsIn.InFcFn = retTemplateFcFn
		} else {
			// 不知道如何处理返回值是 template 的情况
			return nil, false
		}
	}

	// 参数满足 fnTemplateDef 的参数要求
	if templateFcHeadIsIn.InFcFn != nil {
		ok, err = ver.paramsSatisfy_FcFnT_ParamsReq(fc, templateFcHeadIsIn)
	} else {
		ok, err = ver.paramsSatisfy_UserDefinedTemplate_ParamsReq(fc, templateFcHeadIsIn)
	}

	if err != nil {
		return nil, false
	}
	if !ok {
		return nil, false
	}

	// 代入到 retSet 里
	return []env.FnInFnTMemItem{*templateFcIsIn}, true
}

func (ver *Verifier) paramsSatisfy_FcFnT_ParamsReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTMemItem) (bool, error) {
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

func (ver *Verifier) paramsSatisfy_UserDefinedTemplate_ParamsReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTMemItem) (bool, error) {
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

func (ver *Verifier) FcHead_In_FcFnTWhoseRetIsAlsoT(fc *ast.FcFn, fnInFnTMemItem *env.FnInFnTMemItem) (*env.FnInFnTMemItem, *env.FnInFnTMemItem, bool) {
	templateFcHeadIsIn := env.MakeFnInFnTTMemItem(nil, nil)
	templateFcIsIn := env.MakeFnInFnTTMemItem(nil, nil)

	uniMap := map[string]ast.Fc{}
	for i, param := range fnInFnTMemItem.InFcFn.Params {
		uniMap[fnInFnTMemItem.FnTemplateStmt.Params[i]] = param
	}

	InFcFn, err := fnInFnTMemItem.InFcFn.Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	templateFcHeadIsIn.InFcFn = InFcFn.(*ast.FcFn)

	retFcFn, err := templateFcHeadIsIn.InFcFn.Params[0].Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	retFcFnAsFcFn, ok := retFcFn.(*ast.FcFn)
	if !ok {
		return nil, nil, false
	}

	if ast.IsFnTemplate_FcFn(retFcFnAsFcFn) {
		// a(params) 中的 a， 在 fn(..) fn(..)ret
		templateFcIsIn.InFcFn = retFcFn.(*ast.FcFn)
	} else {
		// a(params) 中的 a， 在 fn(..) T(..) 中 (T是某template)
		return nil, nil, false
	}

	return &templateFcHeadIsIn, &templateFcIsIn, true
}
