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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_comparator

import (
	"fmt"
	ast "golitex/ast"
	num "golitex/number"
)

// TODO: 总感觉需要在开头先检查一下left和right确实是多项式。否则随便传个东西过来不太好。
func cmpPolynomial_ByBIR(left ast.Fc, right ast.Fc) bool {
	leftNumerator, leftDenominator, err := num.CombineFractions(left.String())
	if err != nil {
		return false
	}
	rightNumerator, rightDenominator, err := num.CombineFractions(right.String())
	if err != nil {
		return false
	}

	newLeftStr := fmt.Sprintf("%s*%s", leftNumerator, rightDenominator)
	newRightStr := fmt.Sprintf("%s*%s", rightNumerator, leftDenominator)

	// leftStr := num.FcStringForParseAndExpandPolynomial(left)
	// rightStr := num.FcStringForParseAndExpandPolynomial(right)

	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(formattedLeftStr)
	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(formattedRightStr)

	return leftPolyAsStr == rightPolyAsStr
}
