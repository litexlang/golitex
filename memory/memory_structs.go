package memory

import (
	"golitex/parser"
)

type MemoryErr struct {
	err error
}

type SpecificFactMemory struct {
	entries map[string][]SpecFactMemEntry
}
type ForallFactMemory struct {
	entries map[string][]ForallFactMemEntry
}

type SpecFactMemEntry struct {
	tp    parser.PropertyType
	facts []SpecMemFact
}

type SpecMemFact struct {
	fact parser.NotFactStmt
}

type ForallFactMemEntry struct {
	tp    parser.PropertyType
	facts []ForallMemFact
}

type ForallMemFact struct {
	fact parser.ForallStmt
}

type VarMemory map[string]VarMemoryEntry

type VarMemoryEntry struct {
	tp    parser.FcVarType
	types []parser.FcVarType
	decl  parser.FcVarDecl
}

type PropertyMemory map[string]PropertyMemoryEntry

type PropertyMemoryEntry struct {
	tp    parser.PropertyType
	types []parser.PropertyType
	decl  parser.PropertyDecl
}

type FnMemory map[string]FnMemoryEntry

type FnMemoryEntry struct {
	tp    parser.FcFnType
	types []parser.FcFnType
	decl  parser.FcFnDecl
}

type AliasMemory map[string]AliasMemoryEntry

type AliasMemoryEntry struct {
	values *[]parser.Fc
}
