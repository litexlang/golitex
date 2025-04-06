package litexmemory

import (
	parser "golitex/litex_parser"
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

func (mem *PropMem) GetNode(stmt parser.SpecFactStmt) (*StoredPropMemDictNode, bool) {
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
