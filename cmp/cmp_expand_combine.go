package litex_comparator

import (
	ast "golitex/ast"
	num "golitex/number"
)

func CmpPolynomial(left ast.Fc, right ast.Fc) bool {
	leftStr := num.FcStringForParseAndExpandPolynomial(left)
	rightStr := num.FcStringForParseAndExpandPolynomial(right)

	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(leftStr)
	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(rightStr)

	return leftPolyAsStr == rightPolyAsStr
}
