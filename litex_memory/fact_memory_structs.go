package litexmemory

import (
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string variable
type PropName string

type FuncFactMemoryNode = parser.FuncFactStmt

type FuncFactMemory struct {
	Mem RedBlackTree[*FuncFactMemoryNode]
}

type RelationFactMemoryNode = parser.RelationFactStmt

type RelationFactMemory struct {
	Mem RedBlackTree[*RelationFactMemoryNode]
}

type CondFactMemory struct {
	Mem RedBlackTree[*CondFactMemoryNode]
}

type CondFactMemoryNode struct {
	ThenFactAsKey parser.SpecFactStmt
	CondFacts     []*parser.CondFactStmt
}

type UniFactMemory struct {
	Mem RedBlackTree[*UniFactMemoryTreeNode]
}

// ! 如果一个opt是读入2个参数，同时有交换性的，那可以以该fc为key，存所有和它等价的东西的列表
// ! 我感觉这样不太通用。如果是func类型的可交换的prop，那在search的时候有额外能力比较好
// ! 另外，iff 相当于prop 的之间的等于，和var，fn的等号的语义是一样的
type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	Values  []*parser.Fc
}

type EqualFactMemory struct {
	Mem RedBlackTree[*EqualFactMemoryTreeNode]
}

type UniFactMemoryTreeNode struct {
	// TODO
}
