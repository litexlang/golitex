package litexmemory

import (
	parser "golitex/litex_parser"
)

func (memory *PropMem) Insert(stmt *parser.DefConPropStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		// factMem.Dict[PkgName] = map[string]StoredPropMemDictNode{}
		memory.Dict[pkgName] = make(map[string]StoredPropMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = StoredPropMemDictNode{stmt}
	}

	// 更新映射中的节点
	pkgMap[stmt.DefHeader.Name] = node

	return nil
}

func (memory *ObjMem) Insert(stmt *parser.DefObjStmt, pkgName string) error {
	pkgMap, pkgExists := memory.Dict[pkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		// factMem.Dict[PkgName] = map[string]StoredPropMemDictNode{}
		memory.Dict[pkgName] = make(map[string]StoredObjMemDictNode)
		pkgMap = memory.Dict[pkgName]
	}

	// 获取或创建节点
	for _, objName := range stmt.Objs {
		node, nodeExists := pkgMap[objName]
		if !nodeExists {
			node = StoredObjMemDictNode{stmt}
		}
		// 更新映射中的节点
		pkgMap[objName] = node
	}
	return nil
}
