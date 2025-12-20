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

func (envMgr *EnvMgr) GetFnTemplateDef(objAtomName ast.Atom) *ast.FnTemplateDefStmt {
	depthFnTemplateDefPair, ok := envMgr.AllDefinedFnTemplateNames[string(objAtomName)]
	if ok {
		return depthFnTemplateDefPair.defStmt
	}
	return nil
}

func (envMgr *EnvMgr) GetFnTemplateDef_KeyIsObjHead(obj *ast.FnObj) *ast.FnTemplateDefStmt {
	fnHeadAsAtom, ok := obj.FnHead.(ast.Atom)
	if !ok {
		return nil
	}

	fnTemplateDef := envMgr.GetFnTemplateDef(fnHeadAsAtom)
	return fnTemplateDef
}

func (envMgr *EnvMgr) GetSymbolSimplifiedValue(obj ast.Obj) ast.Obj {
	// Search from current depth upward to depth 0
	for depth := envMgr.curEnvDepth(); depth >= 0; depth-- {
		symbolValue, ok := envMgr.EnvSlice[depth].SymbolSimplifiedValueMem[obj.String()]
		if ok {
			return symbolValue
		}
	}
	return nil
}

func (envMgr *EnvMgr) IsCommutativeProp(specFact *ast.SpecFactStmt) bool {
	// Search from current depth upward to depth 0
	for depth := envMgr.curEnvDepth(); depth >= 0; depth-- {
		item, ok := envMgr.EnvSlice[depth].CommutativePropMem[string(specFact.PropName)]
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

func (envMgr *EnvMgr) GetProveAlgoDef(proveAlgoName string) *ast.DefProveAlgoStmt {
	depthProveAlgoDefPair, ok := envMgr.AllDefinedProveAlgoNames[proveAlgoName]
	if ok {
		return depthProveAlgoDefPair.defStmt
	}
	return nil
}

func (envMgr *EnvMgr) GetAlgoDef(funcName string) *ast.DefAlgoStmt {
	depthAlgoDefPair, ok := envMgr.AllDefinedAlgoNames[funcName]
	if ok {
		return depthAlgoDefPair.defStmt
	}
	return nil
}

func (envMgr *EnvMgr) IsFnWithDefinedAlgo(obj ast.Obj) bool {
	objAsFnObj, ok := obj.(*ast.FnObj)
	if !ok {
		return false
	}
	objAsFnObjHeadAsAtom, ok := objAsFnObj.FnHead.(ast.Atom)
	if !ok {
		return false
	}
	return envMgr.GetAlgoDef(objAsFnObjHeadAsAtom.String()) != nil
}
