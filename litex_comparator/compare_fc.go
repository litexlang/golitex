package litexcomparator

import (
	"fmt"
	parser "golitex/litex_parser"
)

func CmpFc(left, right parser.Fc) (int, error) {
	if typeComp, err := compareFcType(left, right); typeComp != 0 || err != nil {
		return typeComp, err
	}

	return compareFcOfTheSameType(left, right)
}

func compareFcType(left, right parser.Fc) (int, error) {
	const (
		fcStrEnum        = 0
		fcFnRetValueEnum = 1
	)

	// Process left
	var knownEnum int
	switch left.(type) {
	case *parser.FcAtom:
		knownEnum = fcStrEnum
	case *parser.FcFnCallPipe:
		knownEnum = fcFnRetValueEnum
	default:
		return 0, fmt.Errorf("unknown Fc type: %T", left)
	}

	// Process right
	var givenEnum int
	switch right.(type) {
	case *parser.FcAtom:
		givenEnum = fcStrEnum
	case *parser.FcFnCallPipe:
		givenEnum = fcFnRetValueEnum
	default:
		return 0, fmt.Errorf("unknown Fc type: %T", right)
	}

	return knownEnum - givenEnum, nil
}

func compareFcOfTheSameType(left, right parser.Fc) (int, error) {
	knownFcAtom, ok := left.(*parser.FcAtom)
	givenFcAtom, ok2 := right.(*parser.FcAtom)
	if ok && ok2 {
		return compareFcAtom(knownFcAtom, givenFcAtom)
	}

	knownFcFnCall, ok := left.(*parser.FcFnCallPipe)
	givenFcFnCall, ok2 := right.(*parser.FcFnCallPipe)
	if ok && ok2 {
		return compareFcFnCallPipe(knownFcFnCall, givenFcFnCall)
	}

	return 0, fmt.Errorf("unknown fc type")
}

func compareFcAtom(left, right *parser.FcAtom) (int, error) {
	if len(left.PkgName) != len(right.PkgName) {
		return len(left.PkgName) - len(right.PkgName), nil
	}

	for i := 0; i < len(left.PkgName); i++ {
		if left.PkgName[i] != right.PkgName[i] {
			return int(left.PkgName[i]) - int(right.PkgName[i]), nil
		}
	}

	if len(left.OptName) != len(right.OptName) {
		return len(left.OptName) - len(right.OptName), nil
	}

	for i := 0; i < len(left.OptName); i++ {
		if left.OptName[i] != right.OptName[i] {
			return int(left.OptName[i]) - int(right.OptName[i]), nil
		}
	}

	return 0, nil
}

func compareFcFnCallPipe(left, right *parser.FcFnCallPipe) (int, error) {
	if comp, err := compareFcAtom(&left.FnName, &right.FnName); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return len(left.CallPipe) - len(right.CallPipe), nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		if comp, err := compareFcFnCallPipeSeg(&left.CallPipe[i], &right.CallPipe[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

func compareFcFnCallPipeSeg(left, right *parser.FcFnCallPipeSeg) (int, error) {
	if len(left.Params) != len(right.Params) {
		return len(left.Params) - len(right.Params), nil
	}

	for i := 0; i < len(left.Params); i++ {
		if comp, err := CmpFc(left.Params[i], right.Params[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
