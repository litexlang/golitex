package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func NewFuncFactMemDict() *FuncFactMemDict {
	return &FuncFactMemDict{map[string]map[string]StoredFuncMemDictNode{}}
}

func (factMem *FuncFactMemDict) Insert(stmt *parser.FuncFactStmt) error {
	pkgMap, pkgExists := factMem.Dict[stmt.Opt.PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		factMem.Dict[stmt.Opt.PkgName] = make(map[string]StoredFuncMemDictNode)
		pkgMap = factMem.Dict[stmt.Opt.PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.Opt.OptName]
	if !nodeExists {
		node = StoredFuncMemDictNode{
			Facts: []StoredFuncFact{},
		}
	}

	// 添加新事实
	node.Facts = append(node.Facts, StoredFuncFact{stmt.IsTrue, stmt.Params})

	// 更新映射中的节点
	pkgMap[stmt.Opt.OptName] = node

	return nil
}

func (factMem *FuncFactMemDict) GetNode(stmt *parser.FuncFactStmt) (*StoredFuncMemDictNode, bool) {
	pkgMap, pkgExists := factMem.Dict[stmt.Opt.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return nil, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.Opt.OptName] // 检查 value 是否存在
	if !nodeExists {
		return nil, false // 返回零值
	}
	return &node, true
}

func NewCondFactMemDict() *CondFactMemDict {
	return &CondFactMemDict{map[string]map[string]StoredCondFuncMemDictNode{}, map[string]map[string]StoredCondRelaMemDictNode{}}
}

func (factMem *CondFactMemDict) Insert(condStmt *parser.CondFactStmt) error {
	for _, stmt := range condStmt.ThenFacts {
		switch s := stmt.(type) {
		case *parser.FuncFactStmt:
			err := factMem.insertFuncFact(condStmt, s)
			if err != nil {
				return err
			}
		case *parser.RelaFactStmt:
			panic("not implemented")
		default:
			return fmt.Errorf("unknown fact type: %T", stmt)
		}
	}
	return nil
}

func (factMem *CondFactMemDict) insertFuncFact(condStmt *parser.CondFactStmt, stmt *parser.FuncFactStmt) error {
	// 检查 pkgName 是否存在，不存在则初始化
	pkgName := stmt.Opt.PkgName
	optName := stmt.Opt.OptName

	if _, pkgExists := factMem.FuncFactsDict[pkgName]; !pkgExists {
		factMem.FuncFactsDict[pkgName] = make(map[string]StoredCondFuncMemDictNode)
	}

	// 获取或初始化节点
	node, nodeExists := factMem.FuncFactsDict[pkgName][optName]
	if !nodeExists {
		node = StoredCondFuncMemDictNode{
			Facts: []StoredCondFuncFact{},
		}
	}

	node.Facts = append(node.Facts, StoredCondFuncFact{stmt.IsTrue, stmt.Params, &condStmt.CondFacts})

	// 更新回字典
	factMem.FuncFactsDict[pkgName][optName] = node
	return nil
}

func (factMem *CondFactMemDict) GetNode(stmt parser.SpecFactStmt) (StoredCondMemDictNode, bool) {
	switch s := stmt.(type) {
	case *parser.FuncFactStmt:
		return factMem.GetFuncFactNode(s)
	case *parser.RelaFactStmt:
		panic("not implemented")
	default:
		panic("invalid type")
	}
}

func (factMem *CondFactMemDict) GetFuncFactNode(stmt *parser.FuncFactStmt) (*StoredCondFuncMemDictNode, bool) {
	pkgName := stmt.Opt.PkgName
	optName := stmt.Opt.OptName

	if _, pkgExists := factMem.FuncFactsDict[pkgName]; !pkgExists {
		return &StoredCondFuncMemDictNode{}, false
	}

	if ret, optExists := factMem.FuncFactsDict[pkgName][optName]; !optExists {
		return &StoredCondFuncMemDictNode{}, false
	} else {
		return &ret, true
	}
}
