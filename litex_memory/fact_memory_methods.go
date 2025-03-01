package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func CompSpecFactParams(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) int {
	return 0
}

func SpecFactCompare(knownFact *parser.SpecFactStmt, givenFact *parser.SpecFactStmt) (int, error) {
	// when two given spec facts are the same in type, compare the value
	knownRelationFact, ok := (*knownFact).(*parser.RelationFactStmt)
	givenRelationFact, ok2 := (*givenFact).(*parser.RelationFactStmt)
	if ok && ok2 {
		return specRelationFactCompare(knownRelationFact, givenRelationFact)
	}

	knownFuncFact, ok := (*knownFact).(*parser.FuncFactStmt)
	givenFuncFact, ok2 := (*givenFact).(*parser.FuncFactStmt)
	if ok && ok2 {
		return specFuncFactCompare(knownFuncFact, givenFuncFact)
	}

	// when two given spec functions are different in type, compare type
	specTypeCompareResult, err := specFactTypeCompare(knownFact, givenFact)
	if err != nil {
		return 0, err
	}
	if specTypeCompareResult != 0 {
		return specTypeCompareResult, nil
	}

	return 0, fmt.Errorf("unknown specFactStmt")
}

func specRelationFactCompare(knownFact *parser.RelationFactStmt, givenFact *parser.RelationFactStmt) (int, error) {
	panic("TODO not implemented")
}

const (
	isTrueEnum    = 0
	isNotTrueEnum = 1
)

func specFuncIsTrueCompare(knownFact *parser.FuncFactStmt, givenFact *parser.FuncFactStmt) int {
	knownFactIsTrueEnum := isTrueEnum
	if !knownFact.IsTrue {
		knownFactIsTrueEnum = isNotTrueEnum
	}

	givenFactIsTrueEnum := isTrueEnum
	if !givenFact.IsTrue {
		givenFactIsTrueEnum = isNotTrueEnum
	}

	return knownFactIsTrueEnum - givenFactIsTrueEnum
}

func specFuncFactCompare(knownFact *parser.FuncFactStmt, givenFact *parser.FuncFactStmt) (int, error) {
	if isTrueComp := specFuncIsTrueCompare(knownFact, givenFact); isTrueComp != 0 {
		return isTrueComp, nil
	}

	return compareFc(knownFact.Fc, givenFact.Fc)
}

const (
	fcStrEnum        = 0
	fcFnRetValueEnum = 1
	FcMemChainEnum   = 2
)

func compareFc(knownFact parser.Fc, givenFact parser.Fc) (int, error) {
	panic("")
}

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

const (
	relationSpecFactStmtEnum = 0
	funcSpecFactEnum         = 1
)

func getSpecFactEnum(fact *parser.SpecFactStmt) (int, error) {

	switch (*fact).(type) {
	case *parser.RelationFactStmt:
		return relationSpecFactStmtEnum, nil
	case *parser.FuncFactStmt:
		return funcSpecFactEnum, nil
	}

	return 0, fmt.Errorf("unknown SpecFactStmt type: %T", *fact)
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
