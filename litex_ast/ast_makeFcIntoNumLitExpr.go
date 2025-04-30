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

package litex_ast

import (
	glob "golitex/litex_global"
)

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

	if IsFcBuiltinUnaryOpt(*asFcFn) {
		ptr, ok := asFcFn.FnHead.(*FcAtom)
		if !ok {
			return nil, false, nil
		}

		if ptr.Name == glob.KeySymbolMinus {
			left, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0][0])
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

	if !IsFcBuiltinInfixOpt(*asFcFn) {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs) != 1 {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs[0]) != 2 {
		return nil, false, nil
	}

	left, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0][0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0][1])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	ptr, ok := asFcFn.FnHead.(*FcAtom)
	if !ok {
		return nil, false, nil
	}
	opt := ptr.Name
	return &glob.NumLitExpr{IsPositive: true, Left: left, OptOrNumber: opt, Right: right}, true, nil
}
