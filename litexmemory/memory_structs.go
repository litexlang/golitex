package litexmemory

import (
	parser "golitex/litexparser"
)

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type SpecificFactMemory struct{ entries map[string]SpecFactMemEntry }

func NewSpecificFactMemory() *SpecificFactMemory {
	return &SpecificFactMemory{entries: map[string]SpecFactMemEntry{}}
}

type SpecFactMemEntry struct{ facts []SpecMemFact }

type SpecMemFact struct{ fact parser.NotFactStmt }

type ForallFactMemory struct{ entires map[string]ForallFactMemEntry }

func NewForallFactMemory() *ForallFactMemory {
	return &ForallFactMemory{map[string]ForallFactMemEntry{}}
}

type ForallFactMemEntry struct{ facts []ForallMemFact }

type ForallMemFact struct{ fact parser.ForallStmt }

type VarMemory struct{ entries map[string]VarMemoryEntry }

func NewVarMemory() *VarMemory {
	return &VarMemory{entries: map[string]VarMemoryEntry{}}
}

type VarMemoryEntry struct {
	tp    parser.FcVarType
	types []parser.FcVarType
}

type PropertyMemory struct {
	entires map[string]PropertyMemoryEntry
}

func NewPropertyMemory() *PropertyMemory {
	return &PropertyMemory{map[string]PropertyMemoryEntry{}}
}

type PropertyMemoryEntry struct {
	tp    parser.FcPropertyType
	types []parser.FcPropertyType
	decl  parser.PropertyDecl
}

type FnMemory struct{ entries map[string]FnMemoryEntry }

func NewFnMemory() *FnMemory {
	return &FnMemory{entries: map[string]FnMemoryEntry{}}
}

type FnMemoryEntry struct {
	tp    parser.FcFnType
	types []parser.FcFnType
	decl  parser.FcFnDecl
}

type AliasMemory struct{ entries map[string]AliasMemoryEntry }

func NewAliasMemory() *AliasMemory {
	return &AliasMemory{map[string]AliasMemoryEntry{}}
}

type AliasMemoryEntry struct {
	values *[]parser.Fc
}
