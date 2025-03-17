package litexmemory

import parser "golitex/litex_parser"

func NewPropMemory() *PropMemory {
	return &PropMemory{}
}
func NewFnMemory() *FnMemory {
	return &FnMemory{}
}

func NewVarMemory() *VarMemory {
	return &VarMemory{}
}

func (mem *VarMemory) Get(s string) (*VarMemoryEntry, bool) {
	panic("TODO")
}

func (mem *VarMemory) Set(pair *parser.FcVarDeclPair) (*VarMemoryEntry, error) {
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

func (env *Env) NewFuncFact(fact *parser.FuncFactStmt) error {
	err := env.FuncFactMemory.Mem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (mem *RelationFactMemory) NewRelationFact(fact *parser.RelationFactStmt) error {
	panic("")
}
