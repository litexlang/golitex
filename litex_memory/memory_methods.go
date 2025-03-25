package litexmemory

import parser "golitex/litex_parser"

func NewPropMemory() *PropMemory {
	return &PropMemory{}
}
func NewFnMemory() *FnMemory {
	return &FnMemory{}
}

func NewObjMemory() *ObjMemory {
	return &ObjMemory{}
}

func (mem *ObjMemory) Get(s string) (*ObjMemoryEntry, bool) {
	panic("TODO")
}

func (mem *ObjMemory) Set(pair string) (*ObjMemoryEntry, error) {
	panic("Todo")
}

func (mem *PropMemory) Get(s string) (*PropMemoryEntry, bool) {
	// TODO
	return nil, false
}

func (mem *FnMemory) Get(s string) (*FnMemEntry, bool) {
	//TODO
	return nil, false
}

func (mem *RelationFactMemory) NewRelationFact(fact *parser.RelationFactStmt) error {
	panic("")
}
