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

type SpecFactMemory struct {
	Entries map[string]SpecFactMemEntry
}

func NewSpecFactMemory() *SpecFactMemory {
	return &SpecFactMemory{Entries: map[string]SpecFactMemEntry{}}
}

type SpecFactMemEntry struct{ Facts []SpecMemoryFact }

type SpecMemoryFact struct {
	then parser.SpecFactStmt // second field is single statement not []
}

type CondFactMemory struct {
	Entries map[string]CondFactMemEntry
}

func NewConditionalFactMemory() *CondFactMemory {
	return &CondFactMemory{Entries: map[string]CondFactMemEntry{}}
}

type CondFactMemEntry struct{ Facts []CondFactMemFact }

type CondFactMemFact struct {
	cond *[]parser.FactStmt
	then parser.FactStmt
}

type UniFactMemory struct{ Entires map[string]UniFactMemEntry }

func NewUniFactMemory() *UniFactMemory {
	return &UniFactMemory{map[string]UniFactMemEntry{}}
}

type UniFactMemEntry struct{ Facts []UniMemFact }

type UniMemFact struct {
	typeParams *[]parser.TypeConceptPair
	varParams  *[]parser.StrTypePair
	cond       *[]parser.FactStmt
	then       *[]parser.SpecFactStmt
}

type VarMemory struct{ Entries map[string]VarMemoryEntry }

func NewVarMemory() *VarMemory {
	return &VarMemory{Entries: map[string]VarMemoryEntry{}}
}

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
