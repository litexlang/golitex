package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func (fact *StoredFuncFact) String(atom parser.FcAtom) string {
	if fact.IsTrue {
		return fmt.Sprintf("%v%s(%s)", parser.KeywordDollar, atom.String(), parser.FcSliceString(&fact.Params))
	}
	return fmt.Sprintf("not %v%s(%s)", parser.KeywordDollar, atom.String(), parser.FcSliceString(&fact.Params))
}

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
	return &CondFactMemDict{map[string]map[string]StoredCondMemDictNode{}}
}

func (factMem *CondFactMemDict) Insert(condStmt *parser.CondFactStmt) error {
	for _, stmt := range condStmt.ThenFacts {
		switch s := stmt.(type) {
		case *parser.FuncFactStmt:
			// 检查 pkgName 是否存在，不存在则初始化
			pkgName := s.Opt.PkgName
			optName := s.Opt.OptName

			if _, pkgExists := factMem.Dict[pkgName]; !pkgExists {
				factMem.Dict[pkgName] = make(map[string]StoredCondMemDictNode)
			}

			// 获取或初始化节点
			node, nodeExists := factMem.Dict[pkgName][optName]
			if !nodeExists {
				node = StoredCondMemDictNode{
					Facts: []StoredCondFact{},
				}
			}

			// TODO: 处理 FuncFactStmt 并更新 node.Facts
			node.Facts = append(node.Facts, StoredCondFact{s.IsTrue, &s.Params, &condStmt.CondFacts})

			// 更新回字典
			factMem.Dict[pkgName][optName] = node

		default:
			return fmt.Errorf("unknown fact type: %T", stmt)
		}
	}
	return nil
}
