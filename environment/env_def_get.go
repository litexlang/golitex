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

func (e *Env) GetFnTemplateDef(fcAtomName ast.FcAtom) *ast.FnTemplateDefStmt {
	for env := e; env != nil; env = env.Parent {
		fnTemplateDef, ok := env.FnTemplateDefMem[string(fcAtomName)]
		if ok {
			return &fnTemplateDef
		}
	}

	return nil
}

func (e *Env) GetFnTemplateDef_KeyIsFcHead(fc *ast.FcFn) *ast.FnTemplateDefStmt {
	fnHeadAsAtom, ok := fc.FnHead.(ast.FcAtom)
	if !ok {
		return nil
	}

	fnTemplateDef := e.GetFnTemplateDef(fnHeadAsAtom)
	return fnTemplateDef
}

func (e *Env) GetExistPropDef(propName ast.FcAtom) *ast.DefExistPropStmt {
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropDefMem[string(propName)]
		if ok {
			return &existProp
		}
	}
	return nil
}

func (e *Env) GetPropDef(propName ast.FcAtom) *ast.DefPropStmt {
	for env := e; env != nil; env = env.Parent {
		prop, ok := env.PropDefMem[string(propName)]
		if ok {
			return &prop
		}
	}
	return nil
}

func (e *Env) GetHaveSetFnDef(fnName ast.FcAtom) *ast.HaveSetFnStmt {
	for env := e; env != nil; env = env.Parent {
		haveSetFn, ok := env.HaveSetFnDefMem[fnName.String()]
		if ok {
			return &haveSetFn
		}
	}
	return nil
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

func (e *Env) GetIntensionalSet(fc ast.Fc) *ast.IntensionalSetStmt {
	for env := e; env != nil; env = env.Parent {
		intensionalSet, ok := env.IntensionalSetMem[fc.String()]
		if ok {
			return &intensionalSet
		}
	}
	return nil
}

func (e *Env) GetSymbolValue(fc ast.Fc) (ast.Fc, bool) {
	for env := e; env != nil; env = env.Parent {
		symbolValue, ok := env.SymbolValueMem[fc.String()]
		if ok {
			return symbolValue, true
		}
	}
	return nil, false
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
