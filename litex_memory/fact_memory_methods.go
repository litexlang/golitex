package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func CompSpecFactParams(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) int {
	return 0
}

func SpecFactCompare(knownFact *parser.SpecFactStmt, givenFact *parser.SpecFactStmt) (int, error) {
	specTypeCompareResult, err := specFactTypeCompare(knownFact, givenFact)
	if err != nil {
		return 0, err
	}

	return specTypeCompareResult, nil
}

const (
	RelationSpecFactStmtEnum = 0
	FuncSpecFactEnum         = 1
)

func specFactTypeCompare(knownFact *parser.SpecFactStmt, givenFact *parser.SpecFactStmt) (int, error) {
	knownFactType, err := getSpecFactEnum(knownFact)
	if err != nil {
		return 0, err
	}

	givenFactType, err := getSpecFactEnum(givenFact)
	if err != nil {
		return 0, err
	}

	return knownFactType - givenFactType, nil
}

func getSpecFactEnum(fact *parser.SpecFactStmt) (int, error) {
	switch (*fact).(type) {
	case *parser.RelationFactStmt:
		return RelationSpecFactStmtEnum, nil
	case *parser.FuncFactStmt:
		return FuncSpecFactEnum, nil
	}

	return 0, fmt.Errorf("Unknown SpecFactStmt type: %T", *fact)
}

func NewSpecFactMemory() *SpecFactMemory {

	return &SpecFactMemory{KnownFacts: RedBlackTree{}}
}

func NewUniFactMemory() *UniFactMemory {
	return &UniFactMemory{map[PropName]UniFactMemEntry{}}
}

func NewCondFactMemory() *CondFactMemory {
	return &CondFactMemory{KVs: map[PropName]CondFactMemEntry{}}
}
