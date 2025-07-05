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
	count := 0
	fcOfEachLevel := []*ast.FcFn{}

	for {
		if headAsAtom, ok := currentFcFn.FnHead.(ast.FcAtom); ok {
			leftMostHead = headAsAtom
			fcOfEachLevel = append([]*ast.FcFn{currentFcFn}, fcOfEachLevel...)
			break
		} else {
			currentFcFn = currentFcFn.FnHead.(*ast.FcFn)
			fcOfEachLevel = append([]*ast.FcFn{currentFcFn}, fcOfEachLevel...)
			count++
		}
	}

	templateOfEachLevel := []*ast.FnTemplateStmt{}

	// get template of leftmost head
	fnT, ok := e.GetLatestFnTemplate(leftMostHead)
	if !ok {
		return nil, nil, false
	}

	templateOfEachLevel = append([]*ast.FnTemplateStmt{fnT}, templateOfEachLevel...)
	fnDefRetSet := fnT.RetSet

	// 从 template 的定义中，得到 template的返回值类型
	for i := count - 1; i >= 0; i-- {
		retSetAtAtom, ok := fnDefRetSet.(ast.FcAtom)
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

	return templateOfEachLevel, fcOfEachLevel, true
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
