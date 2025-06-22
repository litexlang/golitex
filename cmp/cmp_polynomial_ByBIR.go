// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_comparator

import (
	"fmt"
	num "golitex/number"
	parser "golitex/parser"
)

// 超级超级低效的比较方法。无数次的变成string，变回fc，变成string，变回fc
func cmpPolynomial_ByBIR(left string, right string) bool {
	leftNumerator, leftDenominator, err := num.SplitToFraction(left)
	if err != nil {
		return false
	}
	rightNumerator, rightDenominator, err := num.SplitToFraction(right)
	if err != nil {
		return false
	}

	newLeftStr := fmt.Sprintf("(%s)*(%s)", leftNumerator, rightDenominator)
	newRightStr := fmt.Sprintf("(%s)*(%s)", rightNumerator, leftDenominator)

	leftFc, err := parser.ParseSourceCodeGetFc(newLeftStr)
	if err != nil {
		return false
	}
	rightFc, err := parser.ParseSourceCodeGetFc(newRightStr)
	if err != nil {
		return false
	}

	leftStr := num.FcStringForParseAndExpandPolynomial(leftFc)
	rightStr := num.FcStringForParseAndExpandPolynomial(rightFc)

	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(leftStr)
	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(rightStr)

	return leftPolyAsStr == rightPolyAsStr
}

// func cmpPolynomial_ByBIR(left ast.Fc, right ast.Fc) bool {
// 	leftStr := num.FcStringForParseAndExpandPolynomial(left)
// 	rightStr := num.FcStringForParseAndExpandPolynomial(right)

// 	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(leftStr)
// 	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(rightStr)

// 	return leftPolyAsStr == rightPolyAsStr
// }
