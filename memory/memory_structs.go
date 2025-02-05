package memory

import (
	"golitex/parser"
)

type Fc = parser.Fc
type PropertyType = parser.PropertyType
type NotFactStmt = parser.NotFactStmt
type ForallStmt = parser.ForallStmt

type SpecificMemory map[string]SpecificMemEntry

type ForallMemory map[string]ForallMemEntry

type SpecificMemEntry struct {
	tp    PropertyType
	facts []SpecificFact
}

type SpecificFact struct {
	fact NotFactStmt
}

type ForallMemEntry struct {
	tp    PropertyType
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
	tp    PropertyType
	types []PropertyType
	decl  parser.PropertyDecl
}

type FnMemory map[string]FnMemoryEntry

type FnMemoryEntry struct {
	tp    parser.FcFnType
	types []parser.FcFnType
	decl  parser.FcFnDecl
}
