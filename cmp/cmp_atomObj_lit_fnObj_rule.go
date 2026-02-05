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
	ast "golitex/ast"
)

func cmpObjLiterally(left, right ast.Obj) (bool, error) {
	return left.String() == right.String(), nil

	// typeComp, objEnum, err := CmpObjType(left, right)
	// if typeComp != 0 || err != nil {
	// 	return false, err
	// }

	// if objEnum == AtomObjEnum {
	// 	cmp, err := cmpAtomObjLit(left.(ast.Atom), right.(ast.Atom))
	// 	if err != nil {
	// 		return false, err
	// 	}
	// 	return cmp == 0, nil
	// } else if objEnum == FnObjEnum {
	// 	ok, err := cmpFnObjRule(left.(*ast.FnObj), right.(*ast.FnObj))
	// 	if err != nil {
	// 		return false, err
	// 	}
	// 	return ok, nil
	// }

	// return false, fmt.Errorf("")
}

// func cmpFnObjRule(left, right *ast.FnObj) (bool, error) {
// if comp, err := cmpObjLit(left.FnHead, right.FnHead); comp != 0 || err != nil {
// 	return comp == 0, err
// }

// if len(left.Params) != len(right.Params) {
// 	return false, nil
// }

// for i := range len(left.Params) {
// 	ret := CmpByLiteralEqualityAndCalculationAndPolynomialSimplification(left.Params[i], right.Params[i])
// 	if ret.IsNotTrue() {
// 		return false, nil
// 	}
// }

// return true, nil
// }
