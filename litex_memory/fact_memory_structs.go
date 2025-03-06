package litexmemory

import (
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string variable
type PropName string

type FuncFactMemoryNode *parser.FuncFactStmt

type FuncFactMemory struct {
	Mem RedBlackTree[FuncFactMemoryNode]
}

type RelationFactMemoryNode *parser.RelationFactStmt

type RelationFactMemory struct {
	Mem RedBlackTree[RelationFactMemoryNode]
}

type CondFactMemory struct {
	Mem RedBlackTree[CondFactMemoryNode]
}

type CondFactMemoryNodeStruct struct {
	ThenFact  parser.SpecFactStmt
	CondFacts []*parser.CondFactStmt
}

type CondFactMemoryNode *CondFactMemoryNodeStruct

type UniFactMemory struct {
	Mem RedBlackTree[*UniFactMemoryTreeNode]
}

type EqualFactMemoryTreeNode parser.Fc

type EqualFactMemory struct {
	Mem RedBlackTree[*EqualFactMemoryTreeNode]
}

type UniFactMemoryTreeNode struct {
	// TODO
}
