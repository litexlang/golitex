package litexmemory

import (
	ds "golitex/litex_data_structure"
	parser "golitex/litex_parser"
)

type StoredFactStmt interface {
	String(atom parser.FcAtom) string
}

type StoredFuncFact struct {
	IsTrue bool
	Params []parser.Fc
}

type StoredFuncMemDictNode struct{ Facts []StoredFuncFact }
type FuncFactMemDict struct {
	Dict map[string]map[string]StoredFuncMemDictNode
}

type StoredCondMemDictNode interface{ storedCondFuncFact() }

func (m *StoredCondFuncMemDictNode) storedCondFuncFact() {}
func (m *StoredCondRelaMemDictNode) storedCondFuncFact() {}

type StoredCondFuncFact struct {
	IsTrue bool
	Params []parser.Fc
	Fact   *parser.CondFactStmt
}

type StoredCondFuncMemDictNode struct {
	Facts []StoredCondFuncFact
}

type CondFactMemDict struct {
	FuncFactsDict map[string]map[string]StoredCondFuncMemDictNode
	RelaFactsDict map[string]map[string]StoredCondRelaMemDictNode
}

type StoredUniFuncFact struct {
	IsTrue bool
	Params []parser.Fc
	Fact   *parser.UniFactStmt
}

type StoredUniFuncMemDictNode struct {
	Facts []StoredUniFuncFact
}

type UniFactMemDict struct {
	FuncFactsDict   map[string]map[string]StoredUniFuncMemDictNode
	RelaFactMemDict map[string]map[string]StoredUniRelaMemDictNode
}

type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	Values  []*parser.Fc
}

type EqualFactMem struct {
	Mem ds.RedBlackTree[*EqualFactMemoryTreeNode]
}

type RelaFactMemDict struct{}

type StoredCondRelaMemDictNode struct{}
type StoredUniRelaMemDictNode struct{}
