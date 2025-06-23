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

func (e *Env) IsFcAtomDeclared(fcAtomName *ast.FcAtom) bool {
	for env := e; env != nil; env = env.Parent {
		ok := env.isFcAtomDeclaredAtCurEnv(fcAtomName)
		if ok {
			return true
		}
	}
	return false
}

func (e *Env) isFcAtomDeclaredAtCurEnv(fcAtomName *ast.FcAtom) bool {
	_, ok := e.PropDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	_, ok = e.ExistPropDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	_, ok = e.ObjDefMem.Get(*fcAtomName)
	if ok {
		return true
	}

	_, ok = e.FnTemplateDefMem.Get(*fcAtomName)

	return ok
}
