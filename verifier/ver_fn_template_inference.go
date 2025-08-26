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

func (ver *Verifier) GetFnTemplateSliceFcIsIn(fc ast.Fc) ([]env.FnInFnTMemItem, bool) {
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
		return ver.fcHeadIsFcFn_InferTOfFc(fcAsFcFn)
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

	if fnInFnTMemItem.AsFcFn != nil {
		// a(params) 中的a，在 fn(..) fn(..)ret 或 fn(..) T(..) 中
		templateFcHeadIsIn, templateFcIsIn, ok = ver.FcHeadIsAtom_AndIsInFcFnTWhoseRetIsAlsoT(fc, fnInFnTMemItem)
		if !ok {
			return nil, false
		}
	} else {
		// a(params) 中的a，在 T(): fn() T2() 或 T(): fn() fn()Ret 中
		templateFcHeadIsIn, templateFcIsIn, ok = ver.FcHeadIsAtom_AndIsInUserDefinedTemplateWhoseRetIsAlsoFnTemplate(fc, fnInFnTMemItem)
		if !ok {
			return nil, false
		}
	}

	// params 满足 a 所在的 template 的参数要求
	if templateFcHeadIsIn.AsFcFn != nil {
		ok, err = ver.paramsSatisfy_FcFnT_ParamsReq(fc, templateFcHeadIsIn)
	} else {
		ok, err = ver.paramsSatisfy_UserDefinedTemplate_ParamsReq(fc, templateFcHeadIsIn)
	}

	if err != nil || !ok {
		return nil, false
	}

	// 代入到 retSet 里
	return []env.FnInFnTMemItem{*templateFcIsIn}, true
}

func (ver *Verifier) paramsSatisfy_FcFnT_ParamsReq(fcFn *ast.FcFn, fnInFnTTMemItem *env.FnInFnTMemItem) (bool, error) {
	head, ok := fnInFnTTMemItem.AsFcFn.FnHead.(*ast.FcFn)
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
	if len(fcFn.Params) != len(fnInFnTTMemItem.AsFnTStruct.Params) {
		return false, fmt.Errorf("parameters in %s must be %d, %s in %s is not valid", fcFn.FnHead, len(fnInFnTTMemItem.AsFnTStruct.Params), fcFn, fcFn)
	}

	for i := range fcFn.Params {
		inFact := ast.NewInFactWithFc(fcFn.Params[i], fnInFnTTMemItem.AsFnTStruct.ParamSets[i])
		ok, err := ver.VerFactStmt(inFact, Round0NoMsg)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, domFact := range fnInFnTTMemItem.AsFnTStruct.DomFacts {
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

// fc = a(params), a 在 fn(..) fn(..)ret 或 fn(..) T(..) 中，即 a 坐在的template的返回值还是template
func (ver *Verifier) FcHeadIsAtom_AndIsInFcFnTWhoseRetIsAlsoT(fc *ast.FcFn, fnInFnTMemItem *env.FnInFnTMemItem) (*env.FnInFnTMemItem, *env.FnInFnTMemItem, bool) {
	templateFcHeadIsIn := env.MakeFnInFnTTMemItem(nil, nil)
	templateFcIsIn := env.MakeFnInFnTTMemItem(nil, nil)

	uniMap := map[string]ast.Fc{}
	for i, param := range fnInFnTMemItem.AsFcFn.Params {
		uniMap[fnInFnTMemItem.AsFnTStruct.Params[i]] = param
	}

	InFcFn, err := fnInFnTMemItem.AsFcFn.Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	templateFcHeadIsIn.AsFcFn = InFcFn.(*ast.FcFn)

	retFcFn, err := templateFcHeadIsIn.AsFcFn.Params[0].Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	retFcFnAsFcFn, ok := retFcFn.(*ast.FcFn)
	if !ok {
		return nil, nil, false
	}

	if ast.IsFnTemplate_FcFn(retFcFnAsFcFn) {
		// a(params) 中的 a， 在 fn(..) fn(..)ret
		templateFcIsIn.AsFcFn = retFcFn.(*ast.FcFn)
	} else {
		// a(params) 中的 a， 在 fn(..) T(..) 中 (T是某template)
		return nil, nil, false
	}

	return &templateFcHeadIsIn, &templateFcIsIn, true
}

// fc = a(params), a 在 T(): fn() T2() 或 T(): fn() fn()Ret 中，即 a 坐在的template的返回值还是template
func (ver *Verifier) FcHeadIsAtom_AndIsInUserDefinedTemplateWhoseRetIsAlsoFnTemplate(fc *ast.FcFn, fnInFnTMemItem *env.FnInFnTMemItem) (*env.FnInFnTMemItem, *env.FnInFnTMemItem, bool) {
	templateFcHeadIsIn := env.MakeFnInFnTTMemItem(nil, nil)
	templateFcIsIn := env.MakeFnInFnTTMemItem(nil, nil)

	uniMap := map[string]ast.Fc{}
	for i, param := range fnInFnTMemItem.AsFnTStruct.Params {
		uniMap[param] = fc.Params[i]
	}

	inst_template_where_FcHeadIsIn, err := fnInFnTMemItem.AsFnTStruct.Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	templateFcHeadIsIn.AsFnTStruct = inst_template_where_FcHeadIsIn

	retTemplate, err := templateFcHeadIsIn.AsFnTStruct.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, nil, false
	}

	Template_WhereFcIsIn_AsFcFn, ok := retTemplate.(*ast.FcFn)
	if !ok {
		return nil, nil, false
	}

	if ast.IsFnTemplate_FcFn(Template_WhereFcIsIn_AsFcFn) {
		// a(params) 中的 a，在 T(): fn() fn()Ret, retTemplateAsFcFn 是 fn()Ret
		templateFcIsIn.AsFcFn = Template_WhereFcIsIn_AsFcFn
	} else {
		// a(params) 中的 a，在 T(): fn() T2(), retTemplateAsFcFn 是 T2()
		uniMap := map[string]ast.Fc{}
		if len(fc.Params) != len(fnInFnTMemItem.AsFnTStruct.Params) {
			return nil, nil, false
		}

		for i, param := range fnInFnTMemItem.AsFnTStruct.Params {
			uniMap[param] = fc.Params[i]
		}
		inst_retTemplate, err := Template_WhereFcIsIn_AsFcFn.Instantiate(uniMap)
		if err != nil {
			return nil, nil, false
		}

		inst_retTemplateAsFcFn, ok := inst_retTemplate.(*ast.FcFn)
		if !ok {
			return nil, nil, false
		}

		inst_TFcIsInHeadAsAtom, ok := inst_retTemplateAsFcFn.FnHead.(ast.FcAtom)
		if !ok {
			return nil, nil, false
		}

		defOfT, ok := ver.env.GetFnTemplateDef(inst_TFcIsInHeadAsAtom)
		if !ok {
			return nil, nil, false
		}

		templateFcIsIn.AsFnTStruct, err = defOfT.Instantiate_GetFnTemplateNoName(inst_retTemplateAsFcFn)
		if err != nil {
			return nil, nil, false
		}
	}

	return &templateFcHeadIsIn, &templateFcIsIn, true
}

// 形如 a()()(), a()()()()... 这样的 fc
func (ver *Verifier) fcHeadIsFcFn_InferTOfFc(fc *ast.FcFn) ([]env.FnInFnTMemItem, bool) {
	fnTSlice_whereFcHeadIsIn, ok := ver.GetFnTemplateSliceFcIsIn(fc.FnHead)
	if !ok {
		return nil, false
	}

	latestFnTFcHeadIsIn := fnTSlice_whereFcHeadIsIn[len(fnTSlice_whereFcHeadIsIn)-1]

	if latestFnTFcHeadIsIn.AsFcFn != nil {
		return []env.FnInFnTMemItem{env.MakeFnInFnTTMemItem(latestFnTFcHeadIsIn.AsFcFn, nil)}, true
	} else {
		uniMap := map[string]ast.Fc{}
		if len(fc.Params) != len(latestFnTFcHeadIsIn.AsFnTStruct.Params) {
			return nil, false
		}

		for i, param := range latestFnTFcHeadIsIn.AsFnTStruct.Params {
			uniMap[param] = fc.Params[i]
		}
		inst_retTemplate, err := latestFnTFcHeadIsIn.AsFnTStruct.RetSet.Instantiate(uniMap)
		if err != nil {
			return nil, false
		}

		inst_retTemplateAsFcFn, ok := inst_retTemplate.(*ast.FcFn)
		if !ok {
			return nil, false
		}

		inst_TFcIsInHeadAsAtom, ok := inst_retTemplateAsFcFn.FnHead.(ast.FcAtom)
		if !ok {
			return nil, false
		}

		defOfT, ok := ver.env.GetFnTemplateDef(inst_TFcIsInHeadAsAtom)
		if !ok {
			return nil, false
		}

		inst_templateFcIsIn, err := defOfT.Instantiate_GetFnTemplateNoName(inst_retTemplateAsFcFn)
		if err != nil {
			return nil, false
		}

		return []env.FnInFnTMemItem{env.MakeFnInFnTTMemItem(nil, inst_templateFcIsIn)}, true
	}
}
