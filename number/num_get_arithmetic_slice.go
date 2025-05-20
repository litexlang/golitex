package litex_num

import ast "golitex/ast"

func get_fc_slice_of_add(fcFn *ast.FcFn) ([]ast.Fc, error) {
	orderedLeft, err := orderArithmeticExpr_GetOrderedFcSlice(fcFn.ParamSegs[0])
	if err != nil {
		return nil, err
	}
	orderedRight, err := orderArithmeticExpr_GetOrderedFcSlice(fcFn.ParamSegs[1])
	if err != nil {
		return nil, err
	}

	merged := append(orderedLeft, orderedRight...)
	if err != nil {
		return nil, err
	}

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
