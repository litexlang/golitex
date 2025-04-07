package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	cmp "golitex/litex_comparator"
)

func (ver *Verifier) fcEqualSpec(left, right ast.Fc, state VerState) (bool, error) {
	// Case: 全部都是builtin类型：比如int,float。然后里面可能进行1+2=3这样的验证。如果传入的压根不包含builtinFc那就返回false
	ok, err := fcEqualBuiltin(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// Case: 完全一样
	cmpRet, err := cmp.CmpFcLiterally(left, right)
	if err != nil {
		return false, err
	}
	if cmpRet == 0 {
		return true, nil
	}

	// Case: 用已知事实
	nextState := state.spec()
	ok, err = ver.fcEqualSpecInSpecMem(left, right, nextState)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// Case: 如果left, right都是 FcFn，那一位位比较一下
	cmpRet, fcEnum, err := cmp.CmpFcType(left, right)
	if err != nil {
		return false, err
	}

	if cmpRet != 0 {
		// ver.unknownNoMsg()
		return false, nil
	}

	if fcEnum == cmp.FcFnCallPipeEnum {
		return ver.fcFnPipeEqual(left.(*ast.FcFnPipe), right.(*ast.FcFnPipe), SpecMsg)
	} else if fcEnum == cmp.FcAtomEnum {
		return false, nil
	}

	return false, fmt.Errorf("unexpected")
}

func (ver *Verifier) fcEqualSpecInSpecMem(left, right ast.Fc, state VerState) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		verified, err := ver.FcEqualSpecInSpecMemLiterallyAtEnv(curEnv, left, right, state)
		if err != nil {
			return false, err
		}
		if verified {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) FcSliceEqual(left []ast.Fc, right []ast.Fc, specMode VerState) (bool, error) {
	if len(left) != len(right) {
		return false, fmt.Errorf("%v and %v have different length", left, right)
	}

	twoSpecFactHaveEqualParams := true
	for i, knownParam := range left {
		verified, err := ver.FcEqual(knownParam, right[i], specMode)
		if err != nil {
			return false, err
		}
		if !verified {
			twoSpecFactHaveEqualParams = false
			break
		}
	}

	if twoSpecFactHaveEqualParams {
		return true, nil
	}

	return false, nil
}

// func (ver *Verifier) leftAsNumberStrCmp(left, right ast.Fc) (bool, error) {
// 	numberAsStr := ""
// 	var toCmp ast.Fc = nil

// 	leftAsNumberStr, leftIsNumber := ast.IsNumberAtom(left)
// 	if leftIsNumber {
// 		numberAsStr = leftAsNumberStr
// 		toCmp = right
// 	} else {
// 		rightAsNumberStr, rightIsNumber := ast.IsNumberAtom(right)
// 		if rightIsNumber {
// 			numberAsStr = rightAsNumberStr
// 			toCmp = left
// 		} else {
// 			return false, nil
// 		}
// 	}

// 	return cmp.CmpNumberBuiltin(numberAsStr, toCmp)
// }
