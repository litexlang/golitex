// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func newPropMemory() *PropDefMem {
	return &PropDefMem{make(glob.Map2D[PropMemItem])}
}
func newFnMemory() *FnDefMem {
	return &FnDefMem{make(glob.Map2D[FnMemItem])}
}

func newObjMemory() *ObjDefMem {
	return &ObjDefMem{make(glob.Map2D[ObjMemItem])}
}

func newExistPropMemory() *ExistPropDefMem {
	return &ExistPropDefMem{make(glob.Map2D[ExistPropMemItem])}
}

func newSetMemory() *SetDefMem {
	return &SetDefMem{make(glob.Map2D[SetMemItem])}
}

func (memory *PropDefMem) Insert(stmt *ast.DefPropStmt, pkgName string) error {
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

func (memory *ObjDefMem) Insert(stmt *ast.DefObjStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]ObjMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	for _, objName := range stmt.Objs {
		node, nodeExists := pkgMap[objName]
		if !nodeExists {
			node = ObjMemItem{stmt}
		}
		pkgMap[objName] = node
	}
	return nil
}

func (memory *FnDefMem) Insert(stmt *ast.DefFnStmt, pkgName string) error {
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

func (memory *ExistPropDefMem) Insert(stmt *ast.DefExistPropStmt, pkgName string) error {
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

func (memory *EmitIfSpecFactIsTrueMem) Insert(pkgName string, propName string, emitIfSpecFactIsTrue *ast.UniFactStmt) error {
	if _, ok := memory.Dict[pkgName]; !ok {
		memory.Dict[pkgName] = make(map[string][]ast.UniFactStmt)
	}

	if _, ok := memory.Dict[pkgName][propName]; !ok {
		memory.Dict[pkgName][propName] = []ast.UniFactStmt{}
	}

	memory.Dict[pkgName][propName] = append(memory.Dict[pkgName][propName], *emitIfSpecFactIsTrue)

	return nil
}

func (memory *EmitIfSpecFactIsTrueMem) Get(pkgName string, propName string) ([]ast.UniFactStmt, bool) {
	pkgMap, pkgExists := memory.Dict[pkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[propName]
	if !nodeExists {
		return nil, false
	}
	return node, true
}

func (memory *SetDefMem) Insert(stmt *ast.SetDefSetBuilderStmt) error {
	if _, ok := memory.Dict[glob.EmptyPkg]; !ok {
		memory.Dict[glob.EmptyPkg] = make(map[string]SetMemItem)
	}

	if _, ok := memory.Dict[glob.EmptyPkg][stmt.SetName]; !ok {
		memory.Dict[glob.EmptyPkg][stmt.SetName] = SetMemItem{stmt}
	}

	memory.Dict[glob.EmptyPkg][stmt.SetName] = SetMemItem{stmt}

	return nil
}

func (memory *SetDefMem) Get(pkgName string, setName string) (*ast.SetDefSetBuilderStmt, bool) {
	pkgMap, pkgExists := memory.Dict[pkgName]
	if !pkgExists {
		return nil, false
	}

	node, nodeExists := pkgMap[setName]
	if !nodeExists {
		return nil, false
	}
	return node.Def, true
}
