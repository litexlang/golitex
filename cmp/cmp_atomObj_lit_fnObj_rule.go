// Copyright Jiachen Shen.
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

func cmpObjLiterally(left, right ast.Obj) (bool, error) {
	switch asLeft := left.(type) {
	case ast.Atom:
		switch asRight := right.(type) {
		case ast.Atom:
			return asLeft.String() == asRight.String(), nil
		default:
			return false, fmt.Errorf("unknown type: %T", right)
		}
	case *ast.FnObj:
		switch asRight := right.(type) {
		case *ast.FnObj:
			return asLeft.String() == asRight.String(), nil
		default:
			return false, fmt.Errorf("unknown type: %T", right)
		}
	case *ast.FnSetObj:
		switch asRight := right.(type) {
		case *ast.FnSetObj:
			return cmpFnSetObjLiterally(asLeft, asRight)
		default:
			return false, fmt.Errorf("unknown type: %T", right)
		}
	default:
		panic("TODO: cmpObjLiterally: unknown type: " + fmt.Sprintf("%T", left))
	}
}

func cmpFnSetObjLiterally(left, right *ast.FnSetObj) (bool, error) {
	if left.IsNameEmpty() && right.IsNameEmpty() {
		return left.String() == right.String(), nil
	} else if left.IsNameEmpty() && !right.IsNameEmpty() {
		return false, nil
	} else if !left.IsNameEmpty() && right.IsNameEmpty() {
		return false, nil
	} else {
		panic("\n\nTODO: 如果两个fn set对象都有名字，那应该怎么比较？\n\n")
	}
}
