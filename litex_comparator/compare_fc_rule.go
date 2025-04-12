package litex_comparator

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func CmpFcRule(left, right ast.Fc) (bool, error) {
	// 先验证是不是Number，后验证rule，居然让runtime速度提高了1倍。。。
	ok, err := BuiltinFcEqualRule(left, right)
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

// 先确定left，right都是builtin fc，然后按builtin rule来验证他们相等
func BuiltinFcEqualRule(left, right ast.Fc) (bool, error) {
	// Case1: 二者都是 Number 上进行+-*/^
	ok, err := cmpNumLitExpr(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}

// 之所以叫 Expr，因为可能含有运算符+-*/这样的
func cmpNumLitExpr(left, right ast.Fc) (bool, error) {
	leftAsNumberFc, ok, err := ast.MakeFcIntoNumLitExpr(left)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsNumberFc, ok, err := ast.MakeFcIntoNumLitExpr(right)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	leftAsStr, ok, err := glob.EvalNumLitExprFc(leftAsNumberFc)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	rightAsStr, ok, err := glob.EvalNumLitExprFc(rightAsNumberFc)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	if leftAsStr == "" || rightAsStr == "" {
		return false, nil
	}

	return glob.CmpBigFloat(leftAsStr, rightAsStr) == 0, nil
}
