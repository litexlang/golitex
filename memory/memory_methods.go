package memory

import "golitex/parser"

func (mem *VarMemory) Get(s string) (*VarMemoryEntry, bool) {
	ret, ok := mem.entries[s]
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
	mem.entries[pair.Var] = toStore

	return &toStore, nil
}

func (mem *PropertyMemory) Get(s string) (*VarMemoryEntry, bool) {
	// TODO
	return nil, false
}

func (mem *FnMemory) Get(s string) (*VarMemoryEntry, bool) {
	//TODO
	return nil, false
}
