package litexmemory

import (
	parser "golitex/litex_parser"
)

func NewSpecFactMemDict() *SpecFactMemDict {
	return &SpecFactMemDict{map[string]map[string]StoredSpecMemDictNode{}}
}

func (factMem *SpecFactMemDict) Insert(stmt *parser.SpecFactStmt) error {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		factMem.Dict[stmt.PropName.PkgName] = make(map[string]StoredSpecMemDictNode)
		pkgMap = factMem.Dict[stmt.PropName.PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.PropName.Value]
	if !nodeExists {
		node = StoredSpecMemDictNode{
			Facts: []StoredSpecFact{},
		}
	}

	// 添加新事实
	node.Facts = append(node.Facts, StoredSpecFact{stmt.IsTrue, stmt.Params})

	// 更新映射中的节点
	pkgMap[stmt.PropName.Value] = node

	return nil
}

func (factMem *SpecFactMemDict) GetNode(stmt *parser.SpecFactStmt) (*StoredSpecMemDictNode, bool) {
	pkgMap, pkgExists := factMem.Dict[stmt.PropName.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return nil, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.PropName.Value] // 检查 value 是否存在
	if !nodeExists {
		return nil, false // 返回零值
	}
	return &node, true
}

func NewCondFactMemDict() *CondFactMemDict {
	return &CondFactMemDict{map[string]map[string]StoredCondFuncMemDictNode{}}
}

func (factMem *CondFactMemDict) Insert(condStmt *parser.CondFactStmt) error {
	for _, stmt := range condStmt.ThenFacts {
		err := factMem.InsertSpecFact(condStmt, stmt)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *CondFactMemDict) InsertSpecFact(condStmt *parser.CondFactStmt, stmt *parser.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredCondFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = StoredCondFuncMemDictNode{
			Facts: []StoredCondSpecFact{},
		}
	}

	node.Facts = append(node.Facts, StoredCondSpecFact{stmt.IsTrue, stmt.Params, condStmt})

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *CondFactMemDict) GetSpecFactNode(stmt *parser.SpecFactStmt) (*StoredCondFuncMemDictNode, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return &StoredCondFuncMemDictNode{}, false
	}

	if ret, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return &StoredCondFuncMemDictNode{}, false
	} else {
		return &ret, true
	}
}

func (factMem *UniFactMemDict) Insert(fact *parser.UniFactStmt) error {
	for _, stmt := range fact.ThenFacts {
		err := factMem.insertSpecFact(fact, stmt)
		if err != nil {
			return err
		}
	}
	return nil
}

func (factMem *UniFactMemDict) insertSpecFact(uniStmt *parser.UniFactStmt, stmt *parser.SpecFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		factMem.SpecFactsDict[pkgName] = make(map[string]StoredUniFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.SpecFactsDict[pkgName][optName]
	if !nodeExists {
		node = StoredUniFuncMemDictNode{
			Facts: []StoredUniSpecFact{},
		}
	}

	node.Facts = append(node.Facts, StoredUniSpecFact{stmt.IsTrue, &stmt.Params, uniStmt})

	// 更新回字典
	factMem.SpecFactsDict[pkgName][optName] = node
	return nil
}

func NewUniFactMemDict() *UniFactMemDict {
	return &UniFactMemDict{map[string]map[string]StoredUniFuncMemDictNode{}}
}

func (factMem *UniFactMemDict) GetSpecFactNode(stmt *parser.SpecFactStmt) (*StoredUniFuncMemDictNode, bool) {
	pkgName := stmt.PropName.PkgName
	optName := stmt.PropName.Value

	if _, pkgExists := factMem.SpecFactsDict[pkgName]; !pkgExists {
		return &StoredUniFuncMemDictNode{}, false
	}

	if ret, optExists := factMem.SpecFactsDict[pkgName][optName]; !optExists {
		return &StoredUniFuncMemDictNode{}, false
	} else {
		return &ret, true
	}
}
