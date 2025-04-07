package litex_comparator

import (
	"fmt"
	ast "golitex/litex_ast"
)

func cmpFcAtomLitFcFnRule(left, right ast.Fc) (bool, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return false, err
	}

	if fcEnum == FcAtomEnum {
		cmp, err := cmpFcAtomLiteral(left.(*ast.FcAtom), right.(*ast.FcAtom))
		if err != nil {
			return false, err
		}
		return cmp == 0, nil
	} else if fcEnum == FcFnCallPipeEnum {
		// cmp, err := cmpFcFnCallPipeLiterally(left.(*ast.FcFnPipe), right.(*ast.FcFnPipe))
		ok, err := cmpFcFnRule(left.(*ast.FcFn), right.(*ast.FcFn))
		if err != nil {
			return false, err
		}
		return ok, nil
	}

	return false, fmt.Errorf("")
}

func cmpFcFnRule(left, right *ast.FcFn) (bool, error) {
	if comp, err := cmpFcAtomLiteral(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
		return comp == 0, err
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return false, nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		ok, err := cmpFcFnSegRule(left.CallPipe[i], right.CallPipe[i])
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func cmpFcFnSegRule(left, right *ast.FcFnSeg) (bool, error) {
	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	for i := 0; i < len(left.Params); i++ {
		ok, err := CmpFcRule(left.Params[i], right.Params[i])
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
