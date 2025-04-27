// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import ast "golitex/litex_ast"

type StoredPropMemDictNode struct{ Def *ast.DefConPropStmt }

type PropMem struct {
	// 之所以是 map[string][string] 而不是 map[string]，因为虽然用户在当前的项目里，始终第一个key是""，但如果我读入了来自其他地方的包，那就是另外一个名字了
	Dict map[string]map[string]StoredPropMemDictNode
}

type StoredExistPropMemDictNode struct{ Def *ast.DefConExistPropStmt }
type ExistPropMem struct {
	Dict map[string]map[string]StoredExistPropMemDictNode
}

type StoredObjMemDictNode struct{ Def *ast.DefObjStmt }
type ObjMem struct {
	Dict map[string]map[string]StoredObjMemDictNode
}

type FnMem struct {
	Dict map[string]map[string]StoredFnMemDictNode
}

type StoredFnMemDictNode struct{ Def *ast.DefConFnStmt }

func NewPropMemory() *PropMem {
	return &PropMem{map[string]map[string]StoredPropMemDictNode{}}
}
func NewFnMemory() *FnMem {
	return &FnMem{map[string]map[string]StoredFnMemDictNode{}}
}

func NewObjMemory() *ObjMem {
	return &ObjMem{map[string]map[string]StoredObjMemDictNode{}}
}

func NewExistPropMemory() *ExistPropMem {
	return &ExistPropMem{map[string]map[string]StoredExistPropMemDictNode{}}
}

func (memory *PropMem) Insert(stmt *ast.DefConPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]StoredPropMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = StoredPropMemDictNode{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ObjMem) Insert(stmt *ast.DefObjStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]StoredObjMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	for _, objName := range stmt.Objs {
		node, nodeExists := pkgMap[objName]
		if !nodeExists {
			node = StoredObjMemDictNode{stmt}
		}
		pkgMap[objName] = node
	}
	return nil
}

func (memory *FnMem) Insert(stmt *ast.DefConFnStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]StoredFnMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = StoredFnMemDictNode{stmt}
	}

	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ExistPropMem) Insert(stmt *ast.DefConExistPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]StoredExistPropMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.Def.DefHeader.Name]
	if !nodeExists {
		node = StoredExistPropMemDictNode{stmt}
	}
	pkgMap[stmt.Def.DefHeader.Name] = node

	return nil
}

func (memory *PropMem) Get(fc ast.FcAtom) (*ast.DefConPropStmt, bool) {
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

func (memory *ExistPropMem) Get(fc ast.FcAtom) (*ast.DefConExistPropStmt, bool) {
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
