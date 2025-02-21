package litexmemory

import (
	parser "golitex/litex_parser"
)

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type SpecificFactMemory struct{ Entries map[string]SpecFactMemEntry }

func NewSpecificFactMemory() *SpecificFactMemory {
	return &SpecificFactMemory{Entries: map[string]SpecFactMemEntry{}}
}

type SpecFactMemEntry struct{ Facts []SpecMemFact }

type SpecMemFact struct {
	cond *[]parser.FactStmt  // use pointer to share memory
	then parser.BaseFactStmt // second field is single statement not []
}

type ForallFactMemory struct{ Entires map[string]ForallFactMemEntry }

func NewForallFactMemory() *ForallFactMemory {
	return &ForallFactMemory{map[string]ForallFactMemEntry{}}
}

type ForallFactMemEntry struct{ Facts []ForallMemFact }

type ForallMemFact struct {
	typeParams *[]parser.TypeConceptPair
	varParams  *[]parser.StrTypePair
	cond       *[]parser.FactStmt
	then       *[]parser.BaseFactStmt
}

type VarMemory struct{ Entries map[string]VarMemoryEntry }

func NewVarMemory() *VarMemory {
	return &VarMemory{Entries: map[string]VarMemoryEntry{}}
}

type VarMemoryEntry struct {
	Tp    parser.FcVarType
	Types []parser.FcVarType
}

type PropertyMemory struct {
	Entires map[string]PropertyMemoryEntry
}

func NewPropertyMemory() *PropertyMemory {
	return &PropertyMemory{map[string]PropertyMemoryEntry{}}
}

type PropertyMemoryEntry struct {
	Tp    parser.FcPropertyType
	Types []parser.FcPropertyType
	Decl  parser.PropDecl
}

type FnMemory struct{ entries map[string]FnMemoryEntry }

func NewFnMemory() *FnMemory {
	return &FnMemory{entries: map[string]FnMemoryEntry{}}
}

type FnMemoryEntry struct {
	Tp    parser.FcFnType
	Types []parser.FcFnType
	Decl  parser.FcFnDecl
}

type AliasMemory struct{ entries map[string]AliasMemoryEntry }

func NewAliasMemory() *AliasMemory {
	return &AliasMemory{map[string]AliasMemoryEntry{}}
}

type AliasMemoryEntry struct {
	Values *[]string
}

type FcVarTypeMemory struct{ entries map[string][]parser.FcVarType }

func NewFcVarTypeMemory() *FcVarTypeMemory {
	return &FcVarTypeMemory{entries: map[string][]parser.FcVarType{}}
}
