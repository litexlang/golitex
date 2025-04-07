// The difference between "check equality of " and "check equality of two expressions in verifier" is that

package litex_comparator

import (
	ast "golitex/litex_ast"
)

func CmpFcRule(left, right ast.Fc) (bool, error) {
	// 先验证是不是Number，后验证rule，居然让runtime速度提高了1倍。。。
	ok, err := fcEqualNumLitExpr(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	ok, err = cmpFcAtomLitFcFnRule(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

func fcEqualNumLitExpr(left, right ast.Fc) (bool, error) {
	// Case1: 二者都是 Number 上进行+-*/^
	ok, err := cmpNumLitExpr(left, right)
	if err != nil {
		return false, nil
	}
	if ok {
		return true, nil
	}

	return false, nil
}

// 之所以叫 Expr，因为可能含有运算符+-*/这样的
func cmpNumLitExpr(left, right ast.Fc) (bool, error) {
	leftAsNumberFc, ok, err := getNumLitExpr(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumberFc, ok, err := getNumLitExpr(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	leftAsStr, ok, err := evaluateNumLitFc(leftAsNumberFc)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsStr, ok, err := evaluateNumLitFc(rightAsNumberFc)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if leftAsStr == "" || rightAsStr == "" {
		return false, nil
	}

	return cmpBigFloat(leftAsStr, rightAsStr) == 0, nil
}
