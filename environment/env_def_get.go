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

// func (e *Env) GetFnTemplateDef(fcAtomName ast.FcAtom) (*ast.DefFnTemplateStmt, bool) {
// 	for env := e; env != nil; env = env.Parent {
// 		fnTemplateDef, ok := env.FnTemplateDefMem[string(fcAtomName)]
// 		if ok {
// 			return &fnTemplateDef, true
// 		}
// 	}
// 	return nil, false
// }

func (e *Env) GetFnTemplateDef(fcAtomName ast.FcAtom) (*ast.FnTemplateDefStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		fnTemplateDef, ok := env.FnTemplateDefMem[string(fcAtomName)]
		if ok {
			return &fnTemplateDef, true
		}
	}

	return nil, false
}

func (e *Env) GetExistPropDef(propName ast.FcAtom) (*ast.DefExistPropStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropDefMem[string(propName)]
		if ok {
			return &existProp, true
		}
	}
	return nil, false
}

func (e *Env) GetPropDef(propName ast.FcAtom) (*ast.DefPropStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		prop, ok := env.PropDefMem[string(propName)]
		if ok {
			return &prop, true
		}
	}
	return nil, false
}

func (e *Env) GetHaveSetFnDef(fnName ast.FcAtom) (*ast.HaveSetFnStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		haveSetFn, ok := env.HaveSetFnDefMem[fnName.String()]
		if ok {
			return &haveSetFn, true
		}
	}
	return nil, false
}

func (e *Env) isUserDefinedObj(atom ast.FcAtom) bool {
	for curEnv := e; curEnv != nil; curEnv = curEnv.Parent {
		_, ok := curEnv.ObjDefMem[string(atom)]
		if ok {
			return true
		}
	}
	return false
}
