package litexmemory

import (
	parser "golitex/litex_parser"
)

type FcEnum uint8

const (
	FcStrEnum FcEnum = iota
	FcFnRetValueEnum
	FcFnCallChainEnum
)

type FactParamsContainer struct {
}

type FcEnumsFactsKVPair struct {
	ParamEnums      []FcEnum
	ParamsContainer FactParamsContainer
}

// Define type PropName to signify functionality of a string variable
type PropName string

type SpecFactMemory struct {
	PropFactsMap map[PropName]FcEnumFactsKVPairs
}

type FcEnumFactsKVPairs []FcEnumsFactsKVPair

// TODO

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
	return &SpecFactMemory{PropFactsMap: map[PropName]FcEnumFactsKVPairs{}}
}

func NewUniFactMemory() *UniFactMemory {
	return &UniFactMemory{map[PropName]UniFactMemEntry{}}
}

func NewCondFactMemory() *CondFactMemory {
	return &CondFactMemory{KVs: map[PropName]CondFactMemEntry{}}
}
