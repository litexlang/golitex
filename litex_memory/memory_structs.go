package litexmemory

import (
	parser "golitex/litex_parser"
)

// type FnPropParaMemTree struct {
// 	FcStr []parser.FcStr
// }

type VarMemoryEntry struct {
	Tp    parser.FcVarType
	Types []parser.FcVarType
}

type PropMemory struct {
	Entires map[string]PropMemoryEntry
}

func NewPropMemory() *PropMemory {
	return &PropMemory{map[string]PropMemoryEntry{}}
}

type PropMemoryEntry struct {
	Tp    parser.FcPropType
	Types []parser.FcPropType
	Decl  parser.PropDecl
}

type FnMemory struct{ entries map[string]FnMemEntry }

func NewFnMemory() *FnMemory {
	return &FnMemory{entries: map[string]FnMemEntry{}}
}

type FnMemEntry struct {
	Tp    parser.FcFnType
	Types []parser.FcFnType
	Decl  parser.FcFnDecl
}

type AliasMemory struct{ entries map[string]AliasMemEntry }

func NewAliasMemory() *AliasMemory {
	return &AliasMemory{map[string]AliasMemEntry{}}
}

type AliasMemEntry struct {
	Values *[]string
}

type FcVarTypeMemory struct{ entries map[string][]parser.FcVarType }

func NewFcVarTypeMemory() *FcVarTypeMemory {
	return &FcVarTypeMemory{entries: map[string][]parser.FcVarType{}}
}

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type VarMemory struct{ KVs map[string]VarMemoryEntry }

func NewVarMemory() *VarMemory {
	return &VarMemory{KVs: map[string]VarMemoryEntry{}}
}

func NewUniFactMemory() *UniFactMemory {
	// panic("not implemented")
	return &UniFactMemory{}
}
