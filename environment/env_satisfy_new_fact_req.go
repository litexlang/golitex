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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// func (env *Env) AtomsInObjDefinedOrBuiltin(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
// 	// Special handling for setBuilder
// 	if ast.IsSetBuilder(obj) {
// 		return env.AtomsInSetBuilderDefined(obj, extraParams)
// 	}

// 	// Regular object handling
// 	atoms := ast.GetAtomObjsInObj(obj)
// 	for _, atom := range atoms {
// 		if ret := env.IsAtomObjDefinedOrBuiltin(atom, extraParams); ret.IsNotTrue() {
// 			return ret
// 		}
// 	}
// 	return glob.NewGlobTrue("")
// }

// 其实最好要分类：有可能是obj，有可能是prop，不能在验证obj的时候验证是prop

// 这里的name可能是obj，可能是prop
func (e *Env) IsNameDefinedOrBuiltin(name string, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[name]; ok {
		return glob.NewGlobTrue("")
	}

	if glob.IsBuiltinAtom(name) {
		return glob.NewGlobTrue("")
	}

	if e.IsPkgName(name) {
		return glob.NewGlobTrue("")
	}

	if _, ok := ast.IsNumLitAtomObj(ast.Atom(name)); ok {
		return glob.NewGlobTrue("")
	}

	ret := e.IsAtomObjDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
		return glob.NewGlobTrue("")
	}

	existPropDef := e.GetExistPropDef(ast.Atom(name))
	if existPropDef != nil {
		return glob.NewGlobTrue("")
	}

	propDef := e.GetPropDef(ast.Atom(name))
	if propDef != nil {
		return glob.NewGlobTrue("")
	}

	return glob.ErrRet(fmt.Errorf("undefined: %s", name))
}
