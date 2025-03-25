package litexmemory

import (
	"fmt"
	parser "golitex/litex_parser"
)

func specFuncFactCompare(knownFact *FuncFactMemoryNode, givenFact *FuncFactMemoryNode) (int, error) {
	if isTrueComp := specFuncIsTrueCompare(knownFact, givenFact); isTrueComp != 0 {
		return isTrueComp, nil
	}

	return CompareFc(&knownFact.Opt, &givenFact.Opt)
}

func specFuncIsTrueCompare(knownFact *parser.FuncFactStmt, givenFact *parser.FuncFactStmt) int {
	const (
		isTrueEnum    = 0
		isNotTrueEnum = 1
	)

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

func CompareFc(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	if typeComp, err := compareFcType(knownFc, givenFc); typeComp != 0 || err != nil {
		return typeComp, err
	}

	return compareFcOfTheSameType(knownFc, givenFc)
}

func compareFcType(knownFc, givenFc parser.Fc) (int, error) {
	const (
		fcStrEnum        = 0
		fcFnRetValueEnum = 1
	)

	// Process knownFc
	var knownEnum int
	switch knownFc.(type) {
	case *parser.FcAtom:
		knownEnum = fcStrEnum
	case *parser.FcFnRet:
		knownEnum = fcFnRetValueEnum
	default:
		return 0, fmt.Errorf("unknown Fc type: %T", knownFc)
	}

	// Process givenFc
	var givenEnum int
	switch givenFc.(type) {
	case *parser.FcAtom:
		givenEnum = fcStrEnum
	case *parser.FcFnRet:
		givenEnum = fcFnRetValueEnum
	default:
		return 0, fmt.Errorf("unknown Fc type: %T", givenFc)
	}

	return knownEnum - givenEnum, nil
}

func compareFcOfTheSameType(knownFc parser.Fc, givenFc parser.Fc) (int, error) {
	knownFcAtom, ok := knownFc.(*parser.FcAtom)
	givenFcAtom, ok2 := givenFc.(*parser.FcAtom)
	if ok && ok2 {
		return compareFcAtom(knownFcAtom, givenFcAtom)
	}

	knownFcFnRetValue, ok := knownFc.(*parser.FcFnRet)
	givenFcFnRetValue, ok2 := givenFc.(*parser.FcFnRet)
	if ok && ok2 {
		return compareFcFnRetValue(knownFcFnRetValue, givenFcFnRetValue)
	}

	return 0, fmt.Errorf("unknown fc type")
}

func compareFcAtom(knownFc *parser.FcAtom, givenFc *parser.FcAtom) (int, error) {
	if len(knownFc.Value) != len(givenFc.Value) {
		return len(knownFc.Value) - len(givenFc.Value), nil
	}

	for i := 0; i < len(knownFc.Value); i++ {
		if knownFc.Value[i] != givenFc.Value[i] {
			return int(knownFc.Value[i]) - int(givenFc.Value[i]), nil
		}
	}

	return 0, nil
}
