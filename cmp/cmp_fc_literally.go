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

package litex_comparator

import (
	"fmt"
	ast "golitex/ast"
	"strings"
)

type FcEnum uint8

const (
	FcAtomEnum FcEnum = 0
	FcFnEnum   FcEnum = 1
)

func CmpFcType(left, right ast.Obj) (int, FcEnum, error) {
	var knownEnum FcEnum
	switch left.(type) {
	case ast.AtomObj:
		knownEnum = FcAtomEnum
	case *ast.FnObj:
		knownEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", left)
	}

	var givenEnum FcEnum
	switch right.(type) {
	case ast.AtomObj:
		givenEnum = FcAtomEnum
	case *ast.FnObj:
		givenEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
}

// 注：像1+1=2这种字面量的比较，我在这里不比。我是比完完全全一样的
func cmpFcLit(left, right ast.Obj) (int, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if fcEnum == FcAtomEnum {
		return cmpFcAtomLit(left.(ast.AtomObj), right.(ast.AtomObj))
	} else if fcEnum == FcFnEnum {
		return cmpFcFnLit(left.(*ast.FnObj), right.(*ast.FnObj))
	}

	return -1, fmt.Errorf("")
}

func cmpFcAtomLit(left, right ast.AtomObj) (int, error) {
	return strings.Compare(string(left), string(right)), nil // 直接对两个string相减得了
}

func cmpFcFnLit(left, right *ast.FnObj) (int, error) {
	if comp, err := cmpFcLit(left.FnHead, right.FnHead); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.Params) != len(right.Params) {
		return len(left.Params) - len(right.Params), nil
	}

	for i := 0; i < len(left.Params); i++ {
		if comp, err := cmpFcLit(left.Params[i], right.Params[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
