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
		cmp, err := cmpFcAtomLit(left.(*ast.FcAtom), right.(*ast.FcAtom))
		if err != nil {
			return false, err
		}
		return cmp == 0, nil
	} else if fcEnum == FcFnEnum {
		ok, err := cmpFcFnRule(left.(*ast.FcFn), right.(*ast.FcFn))
		if err != nil {
			return false, err
		}
		return ok, nil
	}

	return false, fmt.Errorf("")
}

func cmpFcFnRule(left, right *ast.FcFn) (bool, error) {
	if comp, err := cmpFcAtomLit(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
		return comp == 0, err
	}

	if len(left.ParamSegs) != len(right.ParamSegs) {
		return false, nil
	}

	for i := 0; i < len(left.ParamSegs); i++ {
		ok, err := cmpFcFnSegRule(left.ParamSegs[i], right.ParamSegs[i])
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
