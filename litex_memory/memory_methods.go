package litexmemory

import parser "golitex/litex_parser"

func NewPropMemory() *PropMem {
	return &PropMem{}
}
func NewFnMemory() *FnMem {
	return &FnMem{}
}

func NewObjMemory() *ObjMem {
	return &ObjMem{}
}

func (mem *ObjMem) Get(s string) (*ObjMemoryEntry, bool) {
	panic("TODO")
}

func (mem *ObjMem) Set(pair string) (*ObjMemoryEntry, error) {
	panic("Todo")
}

func (mem *PropMem) Get(s string) (*PropMemoryEntry, bool) {
	// TODO
	return nil, false
}

func (mem *FnMem) Get(s string) (*FnMemEntry, bool) {
	//TODO
	return nil, false
}

func (mem *RelaFactMemory) NewRelaFact(fact *parser.RelaFactStmt) error {
	panic("")
}
