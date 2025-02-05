package memory

import (
	"golitex/parser"
)

type SpecificFactMemory map[string]SpecificMemEntry
type ForallFactMemory map[string]ForallMemEntry

type SpecificMemEntry struct {
	tp    parser.PropertyType
	facts []SpecificFact
}

type SpecificFact struct {
	fact parser.NotFactStmt
}

type ForallMemEntry struct {
	tp    parser.PropertyType
	facts []ForallFact
}

type ForallFact struct {
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
