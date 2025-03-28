package litexcomparator

import (
	"fmt"
	parser "golitex/litex_parser"
)

func CmpFc(left, right parser.Fc) (int, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if fcEnum == FcAtomEnum {
		return cmpFcAtom(left.(*parser.FcAtom), right.(*parser.FcAtom))
	} else if fcEnum == FcFnCallPipeEnum {
		return cmpFcFnCallPipe(left.(*parser.FcFnCallPipe), right.(*parser.FcFnCallPipe))
	}

	return 0, fmt.Errorf("")
}

type FcEnum uint8

const (
	FcAtomEnum       FcEnum = 0
	FcFnCallPipeEnum FcEnum = 1
)

func CmpFcType(left, right parser.Fc) (int, FcEnum, error) {
	var knownEnum FcEnum
	switch left.(type) {
	case *parser.FcAtom:
		knownEnum = FcAtomEnum
	case *parser.FcFnCallPipe:
		knownEnum = FcFnCallPipeEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", left)
	}

	// Process right
	var givenEnum FcEnum
	switch right.(type) {
	case *parser.FcAtom:
		givenEnum = FcAtomEnum
	case *parser.FcFnCallPipe:
		givenEnum = FcFnCallPipeEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
}

func cmpFcAtom(left, right *parser.FcAtom) (int, error) {
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

func cmpFcFnCallPipe(left, right *parser.FcFnCallPipe) (int, error) {
	if comp, err := cmpFcAtom(&left.FnName, &right.FnName); comp != 0 || err != nil {
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
