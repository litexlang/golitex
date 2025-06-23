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

func (e *Env) GetCurrentTemplateOfFc(fc *ast.FcFn) (*ast.FnTemplateStmt, bool) {
	head := fc.FnHead
	if fcHeadAsAtom, ok := head.(*ast.FcAtom); ok {
		fnDef, ok := e.GetLatestFnTemplate(fcHeadAsAtom)
		if !ok {
			return nil, false
		}
		return fnDef, true
	}

	return nil, false
}
