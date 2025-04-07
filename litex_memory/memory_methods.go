package litexmemory

import (
	st "golitex/litex_statements"
)

func NewPropMemory() *PropMem {
	return &PropMem{map[string]map[string]StoredPropMemDictNode{}}
}
func NewFnMemory() *FnMem {
	return &FnMem{map[string]map[string]StoredFnMemDictNode{}}
}

func NewObjMemory() *ObjMem {
	return &ObjMem{map[string]map[string]StoredObjMemDictNode{}}
}

func (mem *PropMem) GetNode(stmt st.SpecFactStmt) (*StoredPropMemDictNode, bool) {
	pkgMap, pkgExists := mem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return nil, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.PropName.Value] // 检查 value 是否存在
	if !nodeExists {
		return nil, false // 返回零值
	}
	return &node, true
}

func (memory *PropMem) Insert(stmt *st.DefConPropStmt, pkgName string) error {
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

func (memory *ObjMem) Insert(stmt *st.DefObjStmt, pkgName string) error {
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

func (memory *FnMem) Insert(stmt *st.DefConFnStmt, pkgName string) error {
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
