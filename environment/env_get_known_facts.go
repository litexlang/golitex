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

func (e *Env) GetFnTemplateOfFc(fn ast.Fc) ([]*ast.FnTemplateStmt, bool) {
	fnDefs := []*ast.FnTemplateStmt{}
	for env := e; env != nil; env = env.Parent {
		fnDefsFromEnv, ok := env.FnInFnTemplateFactsMem.Get(fn)
		if ok {
			fnDefs = append(fnDefs, fnDefsFromEnv...)
		}
	}
	return fnDefs, true
}

// func (e *Env) GetCurrentTemplateOfFc(fc *ast.FcFn) (*ast.FnTemplateStmt, bool) {
// 	fnDef, ok := e.GetLatestFnTemplate(fc.FnHead)
// 	if !ok {
// 		return nil, false
// 	}
// 	return fnDef, true
// }

func (memory FnInFnTemplateFactsMem) Get(fc ast.Fc) ([]*ast.FnTemplateStmt, bool) {
	fnDefs, ok := memory[fc.String()]
	if !ok {
		return nil, false
	}

	return fnDefs, true
}

// return template and parameters of each level of fcFn
// 返回的slice是从左到右的template和params
func (e *Env) GetTemplateOfFcFnRecursively(fcFn *ast.FcFn) ([]*ast.FnTemplateStmt, [][]ast.Fc, bool) {
	currentFcFn := fcFn
	var leftMostHead *ast.FcAtom
	count := 0
	paramsOfEachLevel := [][]ast.Fc{}

	for {
		if headAsAtom, ok := currentFcFn.FnHead.(*ast.FcAtom); ok {
			leftMostHead = headAsAtom
			paramsOfEachLevel = append([][]ast.Fc{currentFcFn.Params}, paramsOfEachLevel...)
			break
		} else {
			currentFcFn = currentFcFn.FnHead.(*ast.FcFn)
			paramsOfEachLevel = append([][]ast.Fc{currentFcFn.Params}, paramsOfEachLevel...)
			count++
		}
	}

	templateOfEachLevel := []*ast.FnTemplateStmt{}

	// get template of leftmost head
	fnT, ok := e.GetLatestFnTemplate(leftMostHead)
	if !ok {
		return nil, nil, false
	}

	templateOfEachLevel = append(templateOfEachLevel, fnT)
	fnDefRetSet := fnT.RetSet

	// 从 template 的定义中，得到 template的返回值类型
	for i := count - 1; i >= 0; i-- {
		retSetAtAtom, ok := fnDefRetSet.(*ast.FcAtom)
		if !ok {
			return nil, nil, false
		}
		templateDef, ok := e.GetFnTemplateDef(retSetAtAtom)
		if !ok {
			return nil, nil, false
		}
		templateOfEachLevel = append(templateOfEachLevel, &templateDef.FnTemplateStmt)
		fnDefRetSet = templateDef.FnTemplateStmt.RetSet
	}

	return templateOfEachLevel, paramsOfEachLevel, true
}
