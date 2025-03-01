package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func CompSpecFactParams(knownFact parser.SpecFactStmt, givenFact parser.SpecFactStmt) int {
	return 0
}

func SpecFactCompare(knownFact *parser.SpecFactStmt, givenFact *parser.SpecFactStmt) (int, error) {
	if specTypeCompareResult, err := specFactTypeCompare(knownFact, givenFact); specTypeCompareResult != 0 || err != nil {
		return specTypeCompareResult, err
	}

	return specFactWithTheSameTypeCompare(knownFact, givenFact)
}

func specFactWithTheSameTypeCompare(knownFact *parser.SpecFactStmt, givenFact *parser.SpecFactStmt) (int, error) {
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

	return 0, fmt.Errorf("unknown spec fact")
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

func getFcEnum(fc parser.Fc) (int, error) {
	_, ok := fc.(parser.FcStr)
	if ok {
		return fcStrEnum, nil
	}

	_, ok = fc.(*parser.FcFnRetValue)
	if ok {
		return fcFnRetValueEnum, nil
	}

	_, ok = fc.(*parser.FcMemChain)
	if ok {
		return FcMemChainEnum, nil
	}

	return 0, fmt.Errorf("unknown Fc type: %T", fc)
}

func compareFc(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	if typeComp, err := compareFcType(knownFc, givenFc); typeComp != 0 || err != nil {
		return typeComp, err
	}

	return compareFcOfTheSameType(knownFc, givenFc)
}

func compareFcOfTheSameType(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	panic("TODO")
}

func compareFcType(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	knownFcEnum, err := getFcEnum(knownFc)
	if err != nil {
		return 0, err
	}

	givenFcEnum, err := getFcEnum(givenFc)
	if err != nil {
		return 0, err
	}

	return knownFcEnum - givenFcEnum, nil
}

const (
	relationSpecFactStmtEnum = 0
	funcSpecFactEnum         = 1
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
