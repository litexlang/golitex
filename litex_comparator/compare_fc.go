package litexcomparator

import (
	"fmt"
	mem "golitex/litex_memory"
	st "golitex/litex_statements"
)

func EqualFactMemoryTreeNodeCompare(left, right *mem.EqualFactMemoryTreeNode) (int, error) {
	return CmpFcLiterally(left.FcAsKey, right.FcAsKey)
}

// 注：像1+1=2这种字面量的比较，我在这里不比。我是比完完全全一样的
func CmpFcLiterally(left, right st.Fc) (int, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if fcEnum == FcAtomEnum {
		return cmpFcAtom(left.(*st.FcAtom), right.(*st.FcAtom))
	} else if fcEnum == FcFnCallPipeEnum {
		return cmpFcFnCallPipe(left.(*st.FcFnPipe), right.(*st.FcFnPipe))
	}

	return 0, fmt.Errorf("")
}

type FcEnum uint8

const (
	FcAtomEnum       FcEnum = 0
	FcFnCallPipeEnum FcEnum = 1
)

func CmpFcType(left, right st.Fc) (int, FcEnum, error) {
	var knownEnum FcEnum
	switch left.(type) {
	case *st.FcAtom:
		knownEnum = FcAtomEnum
	case *st.FcFnPipe:
		knownEnum = FcFnCallPipeEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", left)
	}

	// Process right
	var givenEnum FcEnum
	switch right.(type) {
	case *st.FcAtom:
		givenEnum = FcAtomEnum
	case *st.FcFnPipe:
		givenEnum = FcFnCallPipeEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
}

func cmpFcAtom(left, right *st.FcAtom) (int, error) {
	if len(left.PkgName) != len(right.PkgName) {
		return len(left.PkgName) - len(right.PkgName), nil
	}

	for i := 0; i < len(left.PkgName); i++ {
		if left.PkgName[i] != right.PkgName[i] {
			return int(left.PkgName[i]) - int(right.PkgName[i]), nil
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

func cmpFcFnCallPipe(left, right *st.FcFnPipe) (int, error) {
	if comp, err := cmpFcAtom(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return len(left.CallPipe) - len(right.CallPipe), nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		if comp, err := compareFcFnCallPipeSeg(left.CallPipe[i], right.CallPipe[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

func compareFcFnCallPipeSeg(left, right *st.FcFnPipeSeg) (int, error) {
	if len(left.Params) != len(right.Params) {
		return len(left.Params) - len(right.Params), nil
	}

	for i := 0; i < len(left.Params); i++ {
		if comp, err := CmpFcLiterally(left.Params[i], right.Params[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
