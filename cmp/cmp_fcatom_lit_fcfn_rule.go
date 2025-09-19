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
	ast "golitex/ast"
)

func cmpFcLiterally(left, right ast.Fc) (bool, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return false, err
	}

	if fcEnum == FcAtomEnum {
		cmp, err := cmpFcAtomLit(left.(ast.FcAtom), right.(ast.FcAtom))
		if err != nil {
			return false, err
		}
		return cmp == 0, nil
	} else if fcEnum == FcFnEnum {
		ok, err := cmpFcFnRule(left.(*ast.FcFn), right.(*ast.FcFn))
		if err != nil {
			return false, err
		}
		return ok, nil
	}

	return false, fmt.Errorf("")
}

func cmpFcFnRule(left, right *ast.FcFn) (bool, error) {
	if comp, err := cmpFcLit(left.FnHead, right.FnHead); comp != 0 || err != nil {
		return comp == 0, err
	}

	if len(left.Params) != len(right.Params) {
		return false, nil
	}

	for i := range len(left.Params) {
		ok, _, err := Cmp_ByBIR(left.Params[i], right.Params[i])
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
