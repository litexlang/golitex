package litex_comparator

import (
	"fmt"
	ast "golitex/litex_ast"
)

func cmpFcAtomLiterallyFcFnBuiltin(left, right ast.Fc) (bool, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return false, err
	}

	if fcEnum == FcAtomEnum {
		cmp, err := cmpFcAtomLiterally(left.(*ast.FcAtom), right.(*ast.FcAtom))
		if err != nil {
			return false, err
		}
		return cmp == 0, nil
	} else if fcEnum == FcFnCallPipeEnum {
		// cmp, err := cmpFcFnCallPipeLiterally(left.(*ast.FcFnPipe), right.(*ast.FcFnPipe))
		ok, err := cmpFcFnBuiltin(left.(*ast.FcFnPipe), right.(*ast.FcFnPipe))
		if err != nil {
			return false, err
		}
		return ok, nil
	}

	return false, fmt.Errorf("")
}

func cmpFcFnBuiltin(left, right *ast.FcFnPipe) (bool, error) {
	if comp, err := cmpFcAtomLiterally(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
		return comp == 0, err
	}

	if len(left.CallPipe) != len(right.CallPipe) {
		return false, nil
	}

	for i := 0; i < len(left.CallPipe); i++ {
		ok, err := compareFcFnCallPipeSegBuiltin(left.CallPipe[i], right.CallPipe[i])
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func compareFcFnCallPipeSegBuiltin(left, right *ast.FcFnPipeSeg) (bool, error) {
	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	for i := 0; i < len(left.Params); i++ {
		ok, err := CmpFcBuiltin(left.Params[i], right.Params[i])
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
