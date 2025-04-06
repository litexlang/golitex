package litexverifier

import (
	cmp "golitex/litex_comparator"
	parser "golitex/litex_parser"
)

func (ver *Verifier) fcEqualBuiltin(left, right parser.Fc) (bool, error) {
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

func cmpTwoBuiltinNumberExpressions(left, right parser.Fc) (bool, error) {
	leftAsNumberFc, ok, err := parser.IsNumberFcWithBuiltinInfixOpt(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumberFc, ok, err := parser.IsNumberFcWithBuiltinInfixOpt(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	leftAsStr := cmp.EvaluateNumberFc(leftAsNumberFc)
	rightAsStr := cmp.EvaluateNumberFc(rightAsNumberFc)

	return cmp.CompareBigFloat(leftAsStr, rightAsStr) == 0, nil
}
