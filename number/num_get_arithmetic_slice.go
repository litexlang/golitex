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

import ast "golitex/ast"

func get_fc_slice_of_add(fcFn *ast.FcFn) ([]ast.Fc, error) {
	orderedLeft, err := OrderArithmeticExpr_GetOrderedFcSlice(fcFn.ParamSegs[0])
	if err != nil {
		return nil, err
	}
	orderedRight, err := OrderArithmeticExpr_GetOrderedFcSlice(fcFn.ParamSegs[1])
	if err != nil {
		return nil, err
	}

	merged := append(orderedLeft, orderedRight...)

	return merged, nil
}

func get_fc_slice_of_mul_fcfn(fcFn *ast.FcFn) ([]ast.Fc, error) {
	return []ast.Fc{fcFn}, nil
}

func get_fc_slice_of_minus_as_infix(fcFn *ast.FcFn) ([]ast.Fc, error) {
	return []ast.Fc{fcFn}, nil
}

func get_fc_slice_of_minus_as_prefix(fcFn *ast.FcFn) ([]ast.Fc, error) {
	return []ast.Fc{fcFn}, nil
}
