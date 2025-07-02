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

import ast "golitex/ast"

func Cmp_ByBIR(left, right ast.Fc) (bool, string, error) {
	// case 0: 按字面量来比较。这必须在比较div和比较polynomial之前，因为可能比较的是 * 和 *，即比较两个函数是不是一样。这种函数的比较，跑到div和polynomial就会出问题，因为在那些地方*都会被当成有参数的东西
	ok, err := cmpFcLiterally(left, right)
	if err != nil {
		return false, "", err
	}
	if ok {
		return true, "literally the same", nil
	}

	areNumLit, areEqual, err := NumLitEqual_ByEval(left, right)
	if err != nil {
		return false, "", err
	}
	if areNumLit && areEqual {
		return true, "builtin calculation", nil
	}

	leftStr := left.String()
	rightStr := right.String()

	cmp := cmpPolynomial_ByBIR(leftStr, rightStr)
	if cmp {
		return true, "builtin rules for *, +, -, /", nil
	}

	return false, "", nil
}
