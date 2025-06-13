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

// func isFnWithDivOpt(fc ast.Fc) bool {
// 	asFn, ok := fc.(*ast.FcFn)
// 	if !ok {
// 		return false
// 	}

// 	headAsAtom, ok := asFn.FnHead.(*ast.FcAtom)
// 	if !ok {
// 		return false
// 	}

// 	if headAsAtom.Name == glob.KeySymbolSlash {
// 		return true
// 	}

// 	return false
// }

// // left must be a fc fn with div opt
// func cmpFcFnWithDivOptBuiltinRule(left, right ast.Fc) (bool, error) {
// 	asLeftFn, ok := left.(*ast.FcFn)
// 	if !ok {
// 		return false, errors.New("left is not a function")
// 	}

// 	leftDividend := asLeftFn.ParamSegs[0]
// 	leftDivisor := asLeftFn.ParamSegs[1]

// 	if !isFnWithDivOpt(right) {
// 		leftDivisorMulRightDividend := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{leftDivisor, right})
// 		ok, _, err := Cmp_ByBIR(leftDividend, leftDivisorMulRightDividend)
// 		return ok, err
// 	}

// 	asRightFn, _ := right.(*ast.FcFn)

// 	rightDividend := asRightFn.ParamSegs[0]
// 	rightDivisor := asRightFn.ParamSegs[1]

// 	leftDividendMulRightDivisor := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{leftDividend, rightDivisor})
// 	rightDividendMulLeftDivisor := ast.NewFcFn(ast.NewFcAtomWithName(glob.KeySymbolStar), []ast.Fc{rightDividend, leftDivisor})

// 	ok, _, err := Cmp_ByBIR(leftDividendMulRightDivisor, rightDividendMulLeftDivisor)
// 	return ok, err
// }
