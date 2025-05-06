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

import ast "golitex/litex_ast"

func NewPropMemory() *PropMem {
	return &PropMem{map[string]map[string]PropMemItem{}}
}
func NewFnMemory() *FnMem {
	return &FnMem{map[string]map[string]FnMemItem{}}
}

func NewObjMemory() *ObjMem {
	return &ObjMem{map[string]map[string]ObjMemItem{}}
}

func NewExistPropMemory() *ExistPropMem {
	return &ExistPropMem{map[string]map[string]ExistPropMemItem{}}
}

func (memory *PropMem) Insert(stmt *ast.DefConPropStmt, pkgName string) error {
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

func (memory *ObjMem) Insert(stmt *ast.DefObjStmt, pkgName string) error {
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

func (memory *FnMem) Insert(stmt *ast.DefConFnStmt, pkgName string) error {
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

func (memory *ExistPropMem) Insert(stmt *ast.DefConExistPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName]

	if !pkgExists {
		memory.Dict[pkgName] = make(map[string]ExistPropMemItem)
		pkgMap = memory.Dict[pkgName]
	}

	node, nodeExists := pkgMap[stmt.Def.DefHeader.Name]
	if !nodeExists {
		node = ExistPropMemItem{stmt}
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

func (memory *FnMem) Get(fc ast.FcAtom) (*ast.DefConFnStmt, bool) {
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

func (memory *ObjMem) Get(fc ast.FcAtom) (*ast.DefObjStmt, bool) {
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

func (memory *EmitWhenSpecFactIsTrueMem) Insert(pkgName string, propName string, emitWhenSpecFactIsTrue *ast.UniFactStmt) error {
	if _, ok := memory.Dict[pkgName]; !ok {
		memory.Dict[pkgName] = make(map[string][]EmitWhenSpecFactIsTrueMemItem)
	}

	if _, ok := memory.Dict[pkgName][propName]; !ok {
		memory.Dict[pkgName][propName] = []EmitWhenSpecFactIsTrueMemItem{}
	}

	memory.Dict[pkgName][propName] = append(memory.Dict[pkgName][propName], EmitWhenSpecFactIsTrueMemItem{emitWhenSpecFactIsTrue.Params, emitWhenSpecFactIsTrue.DomFacts})

	return nil
}

func (memory *EmitWhenSpecFactIsTrueMem) Get(pkgName string, propName string) ([]EmitWhenSpecFactIsTrueMemItem, bool) {
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
