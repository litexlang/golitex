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
// Litex Zulip community: https://litex.zulipchat.com

package litex_env

import (
	ast "golitex/ast"
	taskManager "golitex/task_manager"
)

// Insert DefStmt into DefMem

func (memory *PropDefMem) insert(stmt *ast.DefPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]PropMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = PropMemItem{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

// func (memory *ObjDefMem) insert(stmt *ast.DefObjStmt, pkgName string) error {
// 	pkgMap, pkgExists := memory.Dict[pkgName]

// 	if !pkgExists {
// 		memory.Dict[pkgName] = make(map[string]ObjMemItem)
// 		pkgMap = memory.Dict[pkgName]
// 	}

// 	for _, objName := range stmt.Objs {
// 		node, nodeExists := pkgMap[objName]
// 		if !nodeExists {
// 			node = ObjMemItem{stmt}
// 		}
// 		pkgMap[objName] = node
// 	}
// 	return nil
// }

func (memory *FnDefMem) insert(stmt *ast.DefFnStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]FnMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = FnMemItem{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ExistPropDefMem) insert(stmt *ast.DefExistPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]ExistPropMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefBody.DefHeader.Name]
	if !nodeExists {
		node = ExistPropMemItem{stmt}
	}
	pkgMap[stmt.DefBody.DefHeader.Name] = node

	return nil
}

// End of Insert DefStmt into DefMem

// Get DefStmt from DefMem

func (memory *PropDefMem) Get(fc ast.FcAtom) (*ast.DefPropStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}

	return node.Def, true
}

func (memory *ExistPropDefMem) Get(fc ast.FcAtom) (*ast.DefExistPropStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}

func (memory *FnDefMem) Get(fc ast.FcAtom) (*ast.DefFnStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}

func (memory *ObjDefMem) Get(fc ast.FcAtom) (*ast.DefObjStmt, bool) {
	pkgMap, pkgExists := memory.Dict[fc.PkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[fc.Name]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}

// Get Def Recursively From environments

func (e *Env) GetExistPropDef(propName ast.FcAtom) (*ast.DefExistPropStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		existProp, ok := env.ExistPropDefMem.Get(propName)
		if ok {
			return existProp, true
		}
	}
	return nil, false
}

func (e *Env) GetPropDef(propName ast.FcAtom) (*ast.DefPropStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		prop, ok := env.PropDefMem.Get(propName)
		if ok {
			return prop, true
		}
	}
	return nil, false
}

func (e *Env) GetFcAtomDef(fcAtomName *ast.FcAtom) (ast.DefStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		fcAtomDef, ok := env.getFcAtomDefAtCurEnv(fcAtomName)
		if ok {
			return fcAtomDef, true
		}
	}
	return nil, false
}

func (e *Env) GetFnDef(fn ast.Fc) (*ast.DefFnStmt, bool) {
	fnAsAtom, isFnAsAtom := fn.(*ast.FcAtom)
	if !isFnAsAtom {
		return nil, false
	}

	for env := e; env != nil; env = env.Parent {
		fnDef, ok := env.FnDefMem.Get(*fnAsAtom)
		if ok {
			return fnDef, true
		}
	}
	return nil, false
}

// End of Get Def Recursively From environments

// Get DefStmt at current environment

func (e *Env) getFcAtomDefAtCurEnv(fcAtomName *ast.FcAtom) (ast.DefStmt, bool) {
	// Case1: It is a prop
	prop, ok := e.PropDefMem.Get(*fcAtomName)
	if ok {
		return prop, true
	}

	// Case2: It is a fn
	fn, ok := e.FnDefMem.Get(*fcAtomName)
	if ok {
		return fn, true
	}

	// Case3: It is a exist prop
	existProp, ok := e.ExistPropDefMem.Get(*fcAtomName)
	if ok {
		return existProp, true
	}

	// Case4: It is a obj
	obj, ok := e.ObjDefMem.Get(*fcAtomName)
	if ok {
		return obj, true
	}

	return nil, false
}

func (memory *ObjDefMem) InsertItem(objName string) error {
	pkgMap, pkgExists := memory.Dict[taskManager.CurrentPkg]

	if !pkgExists {
		memory.Dict[taskManager.CurrentPkg] = make(map[string]ObjMemItem)
		pkgMap = memory.Dict[taskManager.CurrentPkg]
	}

	node, nodeExists := pkgMap[objName]
	if !nodeExists {
		node = ObjMemItem{nil}
	}

	pkgMap[objName] = node

	return nil
}
