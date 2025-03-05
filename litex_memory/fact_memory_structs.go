package litexmemory

import (
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string variable
type PropName string

type SpecFactMemory struct {
	Mem RedBlackTree[parser.SpecFactStmt]
}

type FuncFactMemory struct {
	Mem RedBlackTree[*parser.FuncFactStmt]
}

type RelationFactMemory struct {
	Mem RedBlackTree[*parser.RelationFactStmt]
}

type CondFactMemory struct {
	Mem RedBlackTree[*CondFactMemoryTreeNode]
}

type CondFactMemoryTreeNode struct {
	ThenFact  parser.SpecFactStmt
	CondFacts []*parser.CondFactStmt
}

type UniFactMemory struct {
	Mem RedBlackTree[*UniFactMemoryTreeNode]
}

type UniFactMemoryTreeNode struct {
	// TODO
}
