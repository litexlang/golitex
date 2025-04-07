package litexverifier

import (
	cmp "golitex/litex_comparator"
	st "golitex/litex_statements"
)

func (ver *Verifier) fcEqualBuiltin(left, right st.Fc) (bool, error) {
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

func cmpTwoBuiltinNumberExpressions(left, right st.Fc) (bool, error) {
	leftAsNumberFc, ok, err := cmp.IsNumberFcWithBuiltinInfixOpt(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumberFc, ok, err := cmp.IsNumberFcWithBuiltinInfixOpt(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	leftAsStr, err := cmp.EvaluateNumberFc(leftAsNumberFc)
	if err != nil {
		return false, err
	}

	rightAsStr, err := cmp.EvaluateNumberFc(rightAsNumberFc)
	if err != nil {
		return false, err
	}

	if leftAsStr == "" || rightAsStr == "" {
		return false, nil
	}

	return cmp.CompareBigFloat(leftAsStr, rightAsStr) == 0, nil
}
