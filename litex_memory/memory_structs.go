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

type InstantiatedFactMemory struct {
	Entries map[string]InstantiatedFactMemEntry
}

func NewInstantiatedFactMemory() *InstantiatedFactMemory {
	return &InstantiatedFactMemory{Entries: map[string]InstantiatedFactMemEntry{}}
}

type InstantiatedFactMemEntry struct{ Facts []InstantiatedMemoryFact }

type InstantiatedMemoryFact struct {
	then parser.InstantiatedFactStmt // second field is single statement not []
}

type ConditionalFactMemory struct {
	Entries map[string]ConditionalFactMemoryEntry
}

func NewConditionalFactMemory() *ConditionalFactMemory {
	return &ConditionalFactMemory{Entries: map[string]ConditionalFactMemoryEntry{}}
}

type ConditionalFactMemoryEntry struct{ Facts []ConditionalFactMemoryFact }

type ConditionalFactMemoryFact struct {
	cond *[]parser.FactStmt
	then parser.FactStmt
}

type UniversalFactMemory struct{ Entires map[string]ForallFactMemEntry }

func NewUniversalFactMemory() *UniversalFactMemory {
	return &UniversalFactMemory{map[string]ForallFactMemEntry{}}
}

type ForallFactMemEntry struct{ Facts []ForallMemFact }

type ForallMemFact struct {
	typeParams *[]parser.TypeConceptPair
	varParams  *[]parser.StrTypePair
	cond       *[]parser.FactStmt
	then       *[]parser.InstantiatedFactStmt
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

func NewPropMemory() *PropertyMemory {
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
