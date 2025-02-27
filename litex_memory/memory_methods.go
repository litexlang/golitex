package litexmemory

import parser "golitex/litex_parser"

func (mem *VarMemory) Get(s string) (*VarMemoryEntry, bool) {
	ret, ok := mem.Entries[s]
	if !ok {
		return nil, false
	}
	return &ret, true
}

func (mem *VarMemory) Set(pair *parser.FcVarDeclPair) (*VarMemoryEntry, error) {
	toStore := VarMemoryEntry{
		pair.Tp,
		[]parser.FcVarType{pair.Tp},
	}
	mem.Entries[pair.Var] = toStore

	return &toStore, nil
}

func (mem *PropMemory) Get(s string) (*PropMemoryEntry, bool) {
	// TODO
	return nil, false
}

func (mem *FnMemory) Get(s string) (*FnMemEntry, bool) {
	//TODO
	return nil, false
}

func (mem *AliasMemory) Get(s string) (*AliasMemEntry, bool) {
	// TODO
	return nil, false
}
