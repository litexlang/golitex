// The difference between "check equality of " and "check equality of two expressions in verifier" is that

package litex_comparator

import (
	ast "golitex/litex_ast"
)

func CmpFcUsingBuiltin(left, right ast.Fc) (bool, error) {
	comp, err := CmpFcLiterally(left, right)
	if err != nil {
		return false, err
	}
	if comp == 0 {
		return true, nil
	}

	ok, err := fcEqualNumber(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func fcEqualNumber(left, right ast.Fc) (bool, error) {
	// Case1: 二者都是 Number 上进行+-*/^
	ok, err := cmpTwoBuiltinNumberExpressions(left, right)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func cmpTwoBuiltinNumberExpressions(left, right ast.Fc) (bool, error) {
	leftAsNumberFc, ok, err := IsNumberFcWithBuiltinInfixOpt(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumberFc, ok, err := IsNumberFcWithBuiltinInfixOpt(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	leftAsStr, err := EvaluateNumberFc(leftAsNumberFc)
	if err != nil {
		return false, err
	}

	rightAsStr, err := EvaluateNumberFc(rightAsNumberFc)
	if err != nil {
		return false, err
	}

	if leftAsStr == "" || rightAsStr == "" {
		return false, nil
	}

	return CompareBigFloat(leftAsStr, rightAsStr) == 0, nil
}
