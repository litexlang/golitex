// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_comparator

import (
	ast "golitex/ast"
	num "golitex/number"
)

func cmpPolynomial(left ast.Fc, right ast.Fc) bool {
	leftStr := num.FcStringForParseAndExpandPolynomial(left)
	rightStr := num.FcStringForParseAndExpandPolynomial(right)

	leftPolyAsStr := num.ExpandPolynomial_ReturnStr(leftStr)
	rightPolyAsStr := num.ExpandPolynomial_ReturnStr(rightStr)

	return leftPolyAsStr == rightPolyAsStr
}
