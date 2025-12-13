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

import ast "golitex/ast"

func (e *Env) GetFnTemplateDef(objAtomName ast.Atom) *ast.FnTemplateDefStmt {
	for env := e; env != nil; env = env.Parent {
		fnTemplateDef, ok := env.FnTemplateDefMem[string(objAtomName)]
		if ok {
			return &fnTemplateDef
		}
	}

	return nil
}

func (e *Env) GetFnTemplateDef_KeyIsObjHead(obj *ast.FnObj) *ast.FnTemplateDefStmt {
	fnHeadAsAtom, ok := obj.FnHead.(ast.Atom)
	if !ok {
		return nil
	}

	fnTemplateDef := e.GetFnTemplateDef(fnHeadAsAtom)
	return fnTemplateDef
}

func (e *Env) GetExistPropDef(propName ast.Atom) *ast.DefExistPropStmt {
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropDefMem[string(propName)]
		if ok {
			return &existProp
		}
	}
	return nil
}

func (e *Env) GetPropDef(propName ast.Atom) *ast.DefPropStmt {
	for env := e; env != nil; env = env.Parent {
		prop, ok := env.PropDefMem[string(propName)]
		if ok {
			return &prop
		}
	}
	return nil
}

func (e *Env) GetSymbolSimplifiedValue(obj ast.Obj) ast.Obj {
	for env := e; env != nil; env = env.Parent {
		symbolValue, ok := env.SymbolSimplifiedValueMem[obj.String()]
		if ok {
			return symbolValue
		}
	}
	return nil
}

func (e *Env) IsCommutativeProp(specFact *ast.SpecFactStmt) bool {
	for env := e; env != nil; env = env.Parent {
		item, ok := env.CommutativePropMem[string(specFact.PropName)]
		if ok {
			if specFact.TypeEnum == ast.TruePure {
				return item.TruePureIsCommutative
			} else if specFact.TypeEnum == ast.FalsePure {
				return item.FalsePureIsCommutative
			}
		}
	}
	return false
}

func (e *Env) GetProveAlgoDef(proveAlgoName string) *ast.DefProveAlgoStmt {
	for env := e; env != nil; env = env.Parent {
		proveAlgoDef, ok := env.DefProveAlgoMem[proveAlgoName]
		if ok {
			return proveAlgoDef
		}
	}
	return nil
}

func (e *Env) IsPkgName(pkgName string) bool {
	_, ok := e.PackageManager.PkgPathNameMgr.NamePathMap[pkgName]
	return ok
}
