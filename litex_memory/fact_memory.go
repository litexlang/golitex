package litexmemory

import (
	parser "golitex/litex_parser"
)

// Define type PropName to signify functionality of a string variable
type PropName string

type SpecFactMemory struct {
	KnownFactsMap map[PropName]KnownSpecPropFactContainer
}

// The dumbest implementation of KnownSpecPropFactContainer: a slice.
type KnownSpecPropFactContainer struct {
	facts []parser.SpecFactStmt
}

type CondFactMemory struct {
	KVs map[PropName]CondFactMemEntry
}

type CondFactMemEntry struct{ Facts []CondFactMemFact }

type CondFactMemFact struct {
	cond *[]parser.FactStmt
	then parser.FactStmt
}

type UniFactMemory struct {
	Entires map[PropName]UniFactMemEntry
}

type UniFactMemEntry struct{ Facts []UniMemFact }

type UniMemFact struct {
	typeParams *[]parser.TypeConceptPair
	varParams  *[]parser.StrTypePair
	cond       *[]parser.FactStmt
	then       *[]parser.SpecFactStmt
}

func NewSpecFactMemory() *SpecFactMemory {
	return &SpecFactMemory{KnownFactsMap: map[PropName]KnownSpecPropFactContainer{}}
}

func NewUniFactMemory() *UniFactMemory {
	return &UniFactMemory{map[PropName]UniFactMemEntry{}}
}

func NewCondFactMemory() *CondFactMemory {
	return &CondFactMemory{KVs: map[PropName]CondFactMemEntry{}}
}
