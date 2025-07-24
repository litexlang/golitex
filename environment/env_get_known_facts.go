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

package litex_env

import ast "golitex/ast"

// return template and parameters of each level of fcFn
// 返回的slice是从左到右的template和params
func (e *Env) GetTemplateOfFcFnRecursively(fcFn *ast.FcFn) ([]*ast.FnTemplateStmt, []*ast.FcFn, bool) {
	currentFcFn := fcFn
	var leftMostHead ast.FcAtom
	paramsOfEachLevel := [][]ast.Fc{currentFcFn.Params}

	for {
		if headAsAtom, ok := currentFcFn.FnHead.(ast.FcAtom); ok {
			leftMostHead = headAsAtom
			break
		} else {
			currentFcFn = currentFcFn.FnHead.(*ast.FcFn)
			paramsOfEachLevel = append([][]ast.Fc{currentFcFn.Params}, paramsOfEachLevel...)
		}
	}

	lenOfParamOfEachLevelMinusOne := len(paramsOfEachLevel) - 1

	templateOfEachLevel := []*ast.FnTemplateStmt{}

	// get template of leftmost head
	fnT, ok := e.GetLatestFnTemplate(leftMostHead)
	if !ok {
		return nil, nil, false
	}

	templateOfEachLevel = append([]*ast.FnTemplateStmt{fnT}, templateOfEachLevel...)
	fnDefRetSet := fnT.RetSet
	fnDefParams := fnT.DefHeader.Params

	// 从 template 的定义中，得到 template的返回值类型
	for i := lenOfParamOfEachLevelMinusOne - 1; i >= 0; i-- {
		switch retT := fnDefRetSet.(type) {
		case ast.FcAtom:
			retT, ok := fnDefRetSet.(ast.FcAtom)
			if !ok {
				return nil, nil, false
			}
			templateDef, ok := e.GetFnTemplateDef(retT)
			if !ok {
				return nil, nil, false
			}
			templateOfEachLevel = append(templateOfEachLevel, &templateDef.FnTemplateStmt)
			fnDefRetSet = templateDef.FnTemplateStmt.RetSet
			fnDefParams = templateDef.FnTemplateStmt.Params
		case *ast.FcFn:
			curLayer := lenOfParamOfEachLevelMinusOne - i - 1

			curParams := paramsOfEachLevel[curLayer]

			if len(curParams) != len(fnDefParams) {
				return nil, nil, false
			}

			uniMap := map[string]ast.Fc{}
			for j, freeVar := range fnDefParams {
				uniMap[freeVar] = curParams[j]
			}

			instRetT, err := retT.Instantiate(uniMap)
			if err != nil {
				return nil, nil, false
			}

			curTemplate, ok := instRetT.(*ast.FcFn).TemplateFcFnToTemplate()
			if !ok {
				return nil, nil, false
			}
			templateOfEachLevel = append(templateOfEachLevel, curTemplate)
			fnDefRetSet = curTemplate.RetSet
		}
	}

	fcFnOfEachLevel := ast.MakeSliceOfFcFnWithHeadAndParamsOfEachLevel(leftMostHead, paramsOfEachLevel)

	return templateOfEachLevel, fcFnOfEachLevel, true
}

func (e *Env) GetEnumFact(enumName string) ([]ast.Fc, bool) {
	for env := e; env != nil; env = env.Parent {
		enumFacts, ok := env.EnumFacts[enumName]
		if ok {
			return enumFacts, true
		}
	}

	return nil, false
}

func (e *Env) GetLatestFnTT_GivenNameIsIn(fnName string) (*FnInFnTTMemItem, bool) {
	for env := e; env != nil; env = env.Parent {
		fnInFnTemplateTemplateFacts, ok := env.FnInFnTemplateTemplateFactsMem[fnName]
		if ok {
			return &fnInFnTemplateTemplateFacts[len(fnInFnTemplateTemplateFacts)-1], true
		}
	}

	return nil, false
}
