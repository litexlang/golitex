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

package litex_ast

import (
	glob "golitex/glob"
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

	if IsFcBuiltinUnaryFn(*asFcFn) {
		ptr, ok := asFcFn.FnHead.(*FcAtom)
		if !ok {
			return nil, false, nil
		}

		if ptr.Name == glob.KeySymbolMinus {
			left, ok, err := MakeFcIntoNumLitExpr(asFcFn.Params[0])
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

	if len(asFcFn.Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := MakeFcIntoNumLitExpr(asFcFn.Params[0])

	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := MakeFcIntoNumLitExpr(asFcFn.Params[1])
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
