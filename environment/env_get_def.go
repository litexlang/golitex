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

func (e *Env) GetFnTemplateDef(fcAtomName *ast.FcAtom) (*ast.DefFnTemplateStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		fnTemplateDef, ok := env.FnTemplateDefMem.Get(*fcAtomName)
		if ok {
			return fnTemplateDef, true
		}
	}
	return nil, false
}

func (e *Env) GetExistPropDef(propName ast.FcAtom) (*ast.DefExistPropStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropDefMem.Get(propName)
		if ok {
			return existProp, true
		}
	}
	return nil, false
}

func (e *Env) GetFcAtomDef(fcAtomName *ast.FcAtom) bool {
	for env := e; env != nil; env = env.Parent {
		ok := env.getFcAtomDefAtCurEnv(fcAtomName)
		if ok {
			return true
		}
	}
	return false
}
