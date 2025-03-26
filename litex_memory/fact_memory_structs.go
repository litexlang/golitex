package litexmemory

import (
	"fmt"
	ds "golitex/litex_data_structure"
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string
type PropName string

type StoredFuncFact struct {
	IsTrue bool
	Params []parser.Fc
}

func (fact *StoredFuncFact) String(atom parser.FcAtom) string {
	if fact.IsTrue {
		return fmt.Sprintf("%v%s(%s)", parser.KeywordDollar, atom.String(), parser.FcSliceString(&fact.Params))
	}
	return fmt.Sprintf("not %v%s(%s)", parser.KeywordDollar, atom.String(), parser.FcSliceString(&fact.Params))
}

type StoredFuncMemDictNode struct{ Facts []StoredFuncFact }
type FuncFactMemDict struct {
	Dict map[string]map[string]StoredFuncMemDictNode
}

func NewFuncFactMemDict() FuncFactMemDict {
	return FuncFactMemDict{map[string]map[string]StoredFuncMemDictNode{}}
}
func (factMem *FuncFactMemDict) InsertConcreteFuncFact(stmt *parser.FuncFactStmt) error {
	pkgMap, pkgExists := factMem.Dict[stmt.Opt.PkgName] // 检查 pkgName 是否存在

	// 如果包不存在，初始化包映射
	if !pkgExists {
		factMem.Dict[stmt.Opt.PkgName] = make(map[string]StoredFuncMemDictNode)
		pkgMap = factMem.Dict[stmt.Opt.PkgName]
	}

	// 获取或创建节点
	node, nodeExists := pkgMap[stmt.Opt.Value]
	if !nodeExists {
		node = StoredFuncMemDictNode{
			Facts: []StoredFuncFact{},
		}
	}

	// 添加新事实
	node.Facts = append(node.Facts, StoredFuncFact{stmt.IsTrue, stmt.Params})

	// 更新映射中的节点
	pkgMap[stmt.Opt.Value] = node

	return nil
}

func (factMem *FuncFactMemDict) GetNode(stmt *parser.FuncFactStmt) (*StoredFuncMemDictNode, bool) {
	pkgMap, pkgExists := factMem.Dict[stmt.Opt.PkgName] // 检查 pkgName 是否存在
	if !pkgExists {
		return nil, false // 返回零值
	}
	node, nodeExists := pkgMap[stmt.Opt.Value] // 检查 value 是否存在
	if !nodeExists {
		return nil, false // 返回零值
	}
	return &node, true
}

// type FuncFactMemoryNode = parser.FuncFactStmt

// type ConcreteFuncFactMemory struct {
// 	Mem ds.RedBlackTree[*FuncFactMemoryNode]
// }

type RelaFactMemory struct{}

type CondFactMemory struct{}

// type RelationFactMemoryNode = parser.RelationFactStmt

// type ConcreteRelationFactMemory struct {
// 	Mem ds.RedBlackTree[*RelationFactMemoryNode]
// }

// type ConcreteCondFactMemory struct {
// 	Mem ds.RedBlackTree[*CondFactMemoryNode]
// }

// type CondFactMemoryNode struct {
// 	ThenFactAsKey parser.SpecFactStmt
// 	CondFacts     []*parser.ConditionalFactStmt
// }

type UniFactMemory struct {
}

// ! 如果一个opt是读入2个参数，同时有交换性的，那可以以该fc为key，存所有和它等价的东西的列表
// ! 我感觉这样不太通用。如果是func类型的可交换的prop，那在search的时候有额外能力比较好
// ! 另外，iff 相当于prop 的之间的等于，和obj，fn的等号的语义是一样的
// ! equalMemory单独拿出来是必要的。它甚至不能和有 ”同时有交换律，结合律“的opt放在一起。原因是 只有 equal 这个性质，会被用于 证明的时候 对一个符号进行等量变换
type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	Values  []*parser.Fc
}

type EqualFactMemory struct {
	Mem ds.RedBlackTree[*EqualFactMemoryTreeNode]
}

type UniFactMemoryTreeNode struct {
	// TODO
}
