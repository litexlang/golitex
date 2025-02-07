package memory

import (
	"golitex/parser"
)

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type SpecificFactMemory map[string]SpecFactMemEntry

type SpecFactMemEntry []SpecMemFact

type SpecMemFact struct{ parser.NotFactStmt }

type ForallFactMemory map[string]ForallFactMemEntry

type ForallFactMemEntry []ForallMemFact

type ForallMemFact struct{ parser.ForallStmt }

type VarMemory map[string]VarMemoryEntry

type VarMemoryEntry struct {
	tp    parser.FcVarType
	types []parser.FcVarType
}

type PropertyMemory map[string]PropertyMemoryEntry

type PropertyMemoryEntry struct {
	tp    parser.FcPropertyType
	types []parser.FcPropertyType
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
