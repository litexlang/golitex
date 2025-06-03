package litex_comparator

import (
	"errors"
	ast "golitex/ast"
	glob "golitex/glob"
)

func isFnWithDivOpt(fc ast.Fc) bool {
	asFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false
	}

	headAsAtom, ok := asFn.FnHead.(*ast.FcAtom)
	if !ok {
		return false
	}

	if headAsAtom.Name == glob.KeySymbolSlash {
		return true
	}

	return false
}

// left must be a fc fn with div opt
func cmpFcFnWithDivOptBuiltinRule(left, right ast.Fc) (bool, error) {
	asLeftFn, ok := left.(*ast.FcFn)
	if !ok {
		return false, errors.New("left is not a function")
	}

	leftDividend := asLeftFn.ParamSegs[0]
	leftDivisor := asLeftFn.ParamSegs[1]

	if !isFnWithDivOpt(right) {
		return false, nil
	}

	asRightFn, ok := right.(*ast.FcFn)
	if !ok {
		leftDivisorMulRightDividend := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{leftDivisor, right})
		return CmpUsingBuiltinRule(leftDivisorMulRightDividend, right)
	}

	rightDividend := asRightFn.ParamSegs[0]
	rightDivisor := asRightFn.ParamSegs[1]

	leftDividendMulRightDivisor := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{leftDividend, rightDivisor})
	rightDividendMulLeftDivisor := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{rightDividend, leftDivisor})

	return CmpUsingBuiltinRule(leftDividendMulRightDivisor, rightDividendMulLeftDivisor)
}
