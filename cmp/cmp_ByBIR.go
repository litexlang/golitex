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

	// case: 如果涉及到的是div运算
	// if isFnWithDivOpt(left) {
	// 	ok, err := cmpFcFnWithDivOptBuiltinRule(left, right)
	// 	if err != nil {
	// 		return false, "", err
	// 	}
	// 	if ok {
	// 		return true, "builtin division rules", nil
	// 	}
	// }
	// if isFnWithDivOpt(right) {
	// 	ok, err := cmpFcFnWithDivOptBuiltinRule(right, left)
	// 	if err != nil {
	// 		return false, "", err
	// 	}
	// 	if ok {
	// 		return true, "builtin division rules", nil
	// 	}
	// }

	// case: 用polynomial rule来比较
	cmp := cmpPolynomial_ByBIR(left.String(), right.String())
	if cmp {
		return true, "builtin polynomial expand and combine rules", nil
	}

	return false, "", nil
}
