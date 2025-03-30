package litexmemory

import (
	ds "golitex/litex_data_structure"
	parser "golitex/litex_parser"
)

type StoredFactStmt interface {
	String(atom parser.FcAtom) string
}

type StoredSpecFact struct {
	IsTrue bool
	Params []parser.Fc
}

type StoredSpecMemDictNode struct{ Facts []StoredSpecFact }
type SpecFactMemDict struct {
	Dict map[string]map[string]StoredSpecMemDictNode
}

type StoredCondSpecFact struct {
	IsTrue bool
	Params *[]parser.Fc
	Fact   *parser.CondFactStmt
}

type StoredCondFuncMemDictNode struct {
	Facts []StoredCondSpecFact
}

type CondFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredCondFuncMemDictNode
}

type StoredUniSpecFact struct {
	IsTrue     bool
	FuncParams *[]parser.Fc
	UniParams  *[]string
	Fact       *parser.UniFactStmt
}

type StoredUniFuncMemDictNode struct {
	Facts []StoredUniSpecFact
}

type UniFactMemDict struct {
	SpecFactsDict map[string]map[string]StoredUniFuncMemDictNode
}

type EqualFactMemoryTreeNode struct {
	FcAsKey parser.Fc
	Values  []*parser.Fc
}

type EqualFactMem struct {
	Mem ds.RedBlackTree[*EqualFactMemoryTreeNode]
}

type ObjMemoryEntry struct {
}

type PropMem struct {
}

type PropMemoryEntry struct {
}

type FnMem struct {
}

type FnMemEntry struct {
}

type ObjMem struct {
}
