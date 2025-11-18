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

package litex_ast

import (
	glob "golitex/glob"
)

func MakeObjIntoNumLitExpr(obj Obj) (*glob.NumLitExpr, bool, error) {
	// obj is atomObj
	asStr, ok := IsNumLitAtomObj(obj)
	if ok {
		return &glob.NumLitExpr{IsPositive: true, Left: nil, OptOrNumber: asStr, Right: nil}, true, nil
	}

	// obj is fnObj

	asObjFn, ok := obj.(*FnObj)
	if !ok {
		// is atom
		return nil, false, nil
	}

	if IsObjBuiltinUnaryFn(*asObjFn) {
		ptr, ok := asObjFn.FnHead.(AtomObj)
		if !ok {
			return nil, false, nil
		}

		if string(ptr) == glob.KeySymbolMinus {
			left, ok, err := MakeObjIntoNumLitExpr(asObjFn.Params[0])
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

	if !IsObjBuiltinInfixOpt(*asObjFn) {
		return nil, false, nil
	}

	if len(asObjFn.Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := MakeObjIntoNumLitExpr(asObjFn.Params[0])

	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := MakeObjIntoNumLitExpr(asObjFn.Params[1])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	ptr, ok := asObjFn.FnHead.(AtomObj)
	if !ok {
		return nil, false, nil
	}
	opt := string(ptr)
	return &glob.NumLitExpr{IsPositive: true, Left: left, OptOrNumber: opt, Right: right}, true, nil
}
