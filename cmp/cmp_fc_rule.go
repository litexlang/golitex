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
	ast "golitex/ast"
	glob "golitex/glob"
)

func NumLitEqual_ByEval(left, right ast.Fc) (bool, bool, error) {
	leftAsNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(left)
	if err != nil {
		return false, false, err
	}
	if !ok {
		return false, false, nil
	}

	rightAsNumLitExpr, ok, err := ast.MakeFcIntoNumLitExpr(right)
	if err != nil {
		return false, false, err
	}
	if !ok {
		return false, false, nil
	}

	areEqual, err := glob.NumLitExprEqual_ByEval(leftAsNumLitExpr, rightAsNumLitExpr)
	return true, areEqual, err
}

func SliceFcAllEqualToGivenFcBuiltinRule(valuesToBeComped *[]ast.Fc, fcToComp ast.Fc) (bool, error) {
	for _, equalFc := range *valuesToBeComped {
		ok, _, err := Cmp_ByBIR(equalFc, fcToComp)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}

	return false, nil
}
