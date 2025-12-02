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

func (e *Env) GetFnTemplateDef(fcAtomName ast.Atom) *ast.FnTemplateDefStmt {
	for env := e; env != nil; env = env.Parent {
		fnTemplateDef, ok := env.FnTemplateDefMem[string(fcAtomName)]
		if ok {
			return &fnTemplateDef
		}
	}

	return nil
}

func (e *Env) GetFnTemplateDef_KeyIsFcHead(fc *ast.FnObj) *ast.FnTemplateDefStmt {
	fnHeadAsAtom, ok := fc.FnHead.(ast.Atom)
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

func (e *Env) GetHaveSetFnDef(fnName ast.Atom) *ast.HaveSetFnStmt {
	for env := e; env != nil; env = env.Parent {
		haveSetFn, ok := env.HaveSetFnDefMem[fnName.String()]
		if ok {
			return &haveSetFn
		}
	}
	return nil
}

func (e *Env) isUserDefinedObj(atom ast.Atom) bool {
	for curEnv := e; curEnv != nil; curEnv = curEnv.Parent {
		_, ok := curEnv.ObjDefMem[string(atom)]
		if ok {
			return true
		}
	}
	return false
}

func (e *Env) GetIntensionalSet(fc ast.Obj) *ast.IntensionalSetStmt {
	for env := e; env != nil; env = env.Parent {
		intensionalSet, ok := env.IntensionalSetMem[fc.String()]
		if ok {
			return &intensionalSet
		}
	}
	return nil
}

func (e *Env) GetSymbolSimplifiedValue(fc ast.Obj) ast.Obj {
	for env := e; env != nil; env = env.Parent {
		symbolValue, ok := env.SymbolSimplifiedValueMem[fc.String()]
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

// GetObjFromCartSetMemItem returns the ObjFromCartSetMemItem for the given object, or nil if not found
func (e *Env) GetObjFromCartSetMemItem(obj ast.Obj) *ObjFromCartSetMemItem {
	for env := e; env != nil; env = env.Parent {
		item, ok := env.ObjFromCartSetMem[obj.String()]
		if ok {
			return &item
		}
	}
	return nil
}

// GetObjTuple returns the tuple (EqualTo) for the given object, or nil if not found
func (e *Env) GetObjTuple(obj ast.Obj) ast.Obj {
	item := e.GetObjFromCartSetMemItem(obj)
	if item == nil {
		return nil
	}
	return item.EqualToOrNil
}

// GetObjCartSet returns the cart set for the given object, or nil if not found
func (e *Env) GetObjCartSet(obj ast.Obj) *ast.FnObj {
	item := e.GetObjFromCartSetMemItem(obj)
	if item == nil {
		return nil
	}
	return item.CartSetOrNil
}

// HasObjFromCartSetMem checks if the object exists in ObjFromCartSetMem
func (e *Env) HasObjFromCartSetMem(obj ast.Obj) bool {
	return e.GetObjFromCartSetMemItem(obj) != nil
}

// GetCartSetMem returns the cart set for the given object, or nil if not found
func (e *Env) GetCartSetMem(obj ast.Obj) *ast.FnObj {
	for env := e; env != nil; env = env.Parent {
		cartSet, ok := env.CartSetMem[obj.String()]
		if ok {
			return cartSet
		}
	}
	return nil
}

// HasCartSetMem checks if the object exists in CartSetMem
func (e *Env) HasCartSetMem(obj ast.Obj) bool {
	return e.GetCartSetMem(obj) != nil
}
