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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_comparator

import (
	"fmt"
	num "golitex/number"
	parser "golitex/parser"
)

// REMARK REMARK
// TODO
// 超级超级低效的比较方法。无数次的变成string，变回obj，变成string，变回obj
// 大部分的时间都被浪费在这里了
// 应该直接把 left, right 读入，当做普通的按字典序排列的题目，然后运算 +-*/^ 等，然后比较结果。这里的parser不应依赖 litex parser 而是应该直接是 正常四则运算的parser
func cmpArith_ByBIR(left string, right string) bool {
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

	leftObj, err := parser.ParseSourceCodeGetObj(newLeftStr)
	if err != nil {
		return false
	}
	rightObj, err := parser.ParseSourceCodeGetObj(newRightStr)
	if err != nil {
		return false
	}

	leftStr := num.ObjStringForParseAndExpandPolynomial(leftObj)
	rightStr := num.ObjStringForParseAndExpandPolynomial(rightObj)

	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(leftStr)
	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(rightStr)

	return leftPolyAsStr == rightPolyAsStr
}
