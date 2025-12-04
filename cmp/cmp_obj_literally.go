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

type ObjEnum uint8

const (
	AtomObjEnum ObjEnum = 0
	FnObjEnum   ObjEnum = 1
)

func CmpObjType(left, right ast.Obj) (int, ObjEnum, error) {
	var knownEnum ObjEnum
	switch left.(type) {
	case ast.Atom:
		knownEnum = AtomObjEnum
	case *ast.FnObj:
		knownEnum = FnObjEnum
	default:
		return 0, AtomObjEnum, fmt.Errorf("unknown Obj type: %T", left)
	}

	var givenEnum ObjEnum
	switch right.(type) {
	case ast.Atom:
		givenEnum = AtomObjEnum
	case *ast.FnObj:
		givenEnum = FnObjEnum
	default:
		return 0, AtomObjEnum, fmt.Errorf("unknown Obj type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
}

// 注：像1+1=2这种字面量的比较，我在这里不比。我是比完完全全一样的
func cmpObjLit(left, right ast.Obj) (int, error) {
	typeComp, objEnum, err := CmpObjType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if objEnum == AtomObjEnum {
		return cmpAtomObjLit(left.(ast.Atom), right.(ast.Atom))
	} else if objEnum == FnObjEnum {
		return cmpFnObjLit(left.(*ast.FnObj), right.(*ast.FnObj))
	}

	return -1, fmt.Errorf("")
}

func cmpAtomObjLit(left, right ast.Atom) (int, error) {
	return strings.Compare(string(left), string(right)), nil // 直接对两个string相减得了
}

func cmpFnObjLit(left, right *ast.FnObj) (int, error) {
	if comp, err := cmpObjLit(left.FnHead, right.FnHead); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.Params) != len(right.Params) {
		return len(left.Params) - len(right.Params), nil
	}

	for i := 0; i < len(left.Params); i++ {
		if comp, err := cmpObjLit(left.Params[i], right.Params[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
