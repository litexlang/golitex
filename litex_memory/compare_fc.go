package litexmemory

import (
	"fmt"

	parser "golitex/litex_parser"
)

func CompareFc(left, right parser.Fc) (int, error) {
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
	case *parser.FcFnCall:
		knownEnum = fcFnRetValueEnum
	default:
		return 0, fmt.Errorf("unknown Fc type: %T", left)
	}

	// Process right
	var givenEnum int
	switch right.(type) {
	case *parser.FcAtom:
		givenEnum = fcStrEnum
	case *parser.FcFnCall:
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

	knownFcFnCall, ok := left.(*parser.FcFnCall)
	givenFcFnCall, ok2 := right.(*parser.FcFnCall)
	if ok && ok2 {
		return compareFcFnCall(knownFcFnCall, givenFcFnCall)
	}

	return 0, fmt.Errorf("unknown fc type")
}

func compareFcAtom(left, right *parser.FcAtom) (int, error) {
	if len(left.FromPkg) != len(right.FromPkg) {
		return len(left.FromPkg) - len(right.FromPkg), nil
	}

	for i := 0; i < len(left.FromPkg); i++ {
		if left.FromPkg[i] != right.FromPkg[i] {
			return int(left.FromPkg[i]) - int(right.FromPkg[i]), nil
		}
	}

	if len(left.Value) != len(right.Value) {
		return len(left.Value) - len(right.Value), nil
	}

	for i := 0; i < len(left.Value); i++ {
		if left.Value[i] != right.Value[i] {
			return int(left.Value[i]) - int(right.Value[i]), nil
		}
	}

	return 0, nil
}

func compareFcFnCall(left, right *parser.FcFnCall) (int, error) {

	// TODO 25-3-25: REFACTOR

	// 从后往前比较

	if comp, err := compareFcAtom(&left.FnName, &right.FnName); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.ParamPipe) != len(right.ParamPipe) {
		return len(left.ParamPipe) - len(right.ParamPipe), nil
	}

	for i := 0; i < len(left.ParamPipe); i++ {
		if comp, err := compareFcFnParams(left.ParamPipe[i], right.ParamPipe[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
