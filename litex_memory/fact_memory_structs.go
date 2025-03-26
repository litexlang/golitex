package litexmemory

import (
	ds "golitex/litex_data_structure"
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string
type PropName string

type StoredFuncFact struct {
	IsTrue bool
	Params []parser.Fc
}

type StoredFuncMemDictNode struct{ Facts []StoredFuncFact }
type FuncFactMemDict struct {
	Dict map[string]map[string]StoredFuncMemDictNode
}

func NewConcreteFuncFactMemDict() FuncFactMemDict {
	return FuncFactMemDict{map[string]map[string]StoredFuncMemDictNode{}}
}

func (f *FuncFactMemDict) GetNode(stmt *parser.FuncFactStmt) (*StoredFuncMemDictNode, bool) {
	pkgMap, pkgExists := f.Dict[stmt.Opt.PkgName] // 检查 pkgName 是否存在
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

type ConcreteRelationFactMemory struct{}

type ConcreteCondFactMemory struct{}

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

type ConcreteUniFactMemory struct {
}

// ! 如果一个opt是读入2个参数，同时有交换性的，那可以以该fc为key，存所有和它等价的东西的列表
// ! 我感觉这样不太通用。如果是func类型的可交换的prop，那在search的时候有额外能力比较好
// ! 另外，iff 相当于prop 的之间的等于，和obj，fn的等号的语义是一样的
// ! equalMemory单独拿出来是必要的。它甚至不能和有 ”同时有交换律，结合律“的opt放在一起。原因是 只有 equal 这个性质，会被用于 证明的时候 对一个符号进行等量变换
type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	Values  []*parser.Fc
}

type ConcreteEqualFactMemory struct {
	Mem ds.RedBlackTree[*EqualFactMemoryTreeNode]
}

type UniFactMemoryTreeNode struct {
	// TODO
}
