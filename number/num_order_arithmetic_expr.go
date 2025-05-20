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

package litex_num

import (
	"fmt"
	ast "golitex/ast"
)

func orderArithmeticExpr_GetOrderedFcSlice(fc ast.Fc) ([]ast.Fc, error) {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		return orderArithmeticExpr_GetOrderedSlice_FcAtom(asAtom)
	} else if asFcFn, ok := fc.(*ast.FcFn); ok {
		return orderArithmeticExpr_GetOrderedSlice_FcFn(asFcFn)
	}
	return nil, fmt.Errorf("expected arithmetic function, but got %s", fc.String())
}

func orderArithmeticExpr_GetOrderedSlice_FcAtom(fcAtom *ast.FcAtom) ([]ast.Fc, error) {
	return []ast.Fc{fcAtom}, nil
}

func orderArithmeticExpr_GetOrderedSlice_FcFn(fcFn *ast.FcFn) ([]ast.Fc, error) {
	var ret []ast.Fc
	var err error

	if isAdd(fcFn) {
		ret, err = get_fc_slice_of_add(fcFn)
	} else if isMul(fcFn) {
		ret, err = get_fc_slice_of_mul_fcfn(fcFn)
	} else if isMinusAsInfix(fcFn) {
		ret, err = get_fc_slice_of_minus_as_infix(fcFn)
	} else if isMinusAsPrefix(fcFn) {
		ret, err = get_fc_slice_of_minus_as_prefix(fcFn)
	} else {
		return []ast.Fc{fcFn}, nil
	}

	ret, err = orderFcSlice(ret)
	if err != nil {
		return nil, err
	}

	return ret, nil
}

func orderFcSlice(fcSlice []ast.Fc) ([]ast.Fc, error) {
	return fcSlice, nil
}
