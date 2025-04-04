package litexmemory

import (
	parser "golitex/litex_parser"
)

func (factMem *PropMem) Insert(stmt *parser.DefConPropStmt, PkgName string) error {
	pkgMap, pkgExists := factMem.Dict[PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		// factMem.Dict[PkgName] = map[string]StoredPropMemDictNode{}
		factMem.Dict[PkgName] = make(map[string]StoredPropMemDictNode)
		pkgMap = factMem.Dict[PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.DefHeader.Name]
	if !nodeExists {
		node = StoredPropMemDictNode{}
	}

	// 更新映射中的节点
	pkgMap[stmt.DefHeader.Name] = node

	return nil
}
