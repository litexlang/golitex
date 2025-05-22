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

import ast "golitex/ast"

func CmpUsingBuiltinRule(left, right ast.Fc) (bool, error) {
	// case 0: 用polynomial rule来比较
	cmp := CmpPolynomial(left, right)
	if cmp {
		return true, nil
	}

	// case 1: 用number rule来比较
	ok, err := cmpNumLitExpr(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	// case 2: 按字面量来比较
	ok, err = cmpFcLiterally(left, right)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}
