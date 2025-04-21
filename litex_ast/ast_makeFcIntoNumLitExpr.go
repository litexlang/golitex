// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_ast

import (
	glob "golitex/litex_global"
)

func IsFcBuiltinNumLitExpr(left Fc) (*glob.NumLitExpr, bool, error) {
	return MakeFcIntoNumLitExpr(left)
}

func MakeFcIntoNumLitExpr(fc Fc) (*glob.NumLitExpr, bool, error) {
	// fc is fcAtom
	asStr, ok := IsNumLitFcAtom(fc)
	if ok {
		return &glob.NumLitExpr{IsPositive: true, Left: nil, OptOrNumber: asStr, Right: nil}, true, nil
	}

	// fc is fcFn

	asFcFn, ok := fc.(*FcFn)
	if !ok {
		// is atom
		return nil, false, nil
	}

	if asFcFn.FnHead.IsBuiltinUnaryOpt() {
		if asFcFn.FnHead.PropName == glob.KeySymbolMinus {
			left, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0].Params[0])
			if err != nil {
				return nil, false, err
			}
			if !ok {
				return nil, false, nil
			}
			left.IsPositive = false
			return left, true, nil
		}
	}

	if !asFcFn.FnHead.IsBuiltinInfixOpt() {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs) != 1 {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs[0].Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0].Params[0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0].Params[1])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	opt := asFcFn.FnHead.PropName
	return &glob.NumLitExpr{IsPositive: true, Left: left, OptOrNumber: opt, Right: right}, true, nil
}
