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

import (
	"fmt"
	ast "golitex/ast"
)

type FcEnum uint8

const (
	FcAtomEnum FcEnum = 0
	FcFnEnum   FcEnum = 1
)

func CmpFcType(left, right ast.Fc) (int, FcEnum, error) {
	var knownEnum FcEnum
	switch left.(type) {
	case *ast.FcAtom:
		knownEnum = FcAtomEnum
	case *ast.FcFn:
		knownEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", left)
	}

	var givenEnum FcEnum
	switch right.(type) {
	case *ast.FcAtom:
		givenEnum = FcAtomEnum
	case *ast.FcFn:
		givenEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
}

// func EqualFactMemoryTreeNodeCompare(left, right *mem.EqualFactMemoryTreeNode) (int, error) {
// 	return cmpFcLit(left.FcAsKey, right.FcAsKey)
// }

// 注：像1+1=2这种字面量的比较，我在这里不比。我是比完完全全一样的
func cmpFcLit(left, right ast.Fc) (int, error) {
	typeComp, fcEnum, err := CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if fcEnum == FcAtomEnum {
		return cmpFcAtomLit(left.(*ast.FcAtom), right.(*ast.FcAtom))
	} else if fcEnum == FcFnEnum {
		return cmpFcFnLit(left.(*ast.FcFn), right.(*ast.FcFn))
	}

	return -1, fmt.Errorf("")
}

func cmpFcAtomLit(left, right *ast.FcAtom) (int, error) {
	if len(left.PkgName) != len(right.PkgName) {
		return len(left.PkgName) - len(right.PkgName), nil
	}

	for i := 0; i < len(left.PkgName); i++ {
		if left.PkgName[i] != right.PkgName[i] {
			return int(left.PkgName[i]) - int(right.PkgName[i]), nil
		}
	}

	if len(left.Name) != len(right.Name) {
		return len(left.Name) - len(right.Name), nil
	}

	for i := 0; i < len(left.Name); i++ {
		if left.Name[i] != right.Name[i] {
			return int(left.Name[i]) - int(right.Name[i]), nil
		}
	}

	return 0, nil
}

func cmpFcFnLit(left, right *ast.FcFn) (int, error) {
	// if comp, err := cmpFcAtomLit(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
	// 	return comp, err
	// }

	if comp, err := cmpFcLit(left.FnHead, right.FnHead); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.ParamSegs) != len(right.ParamSegs) {
		return len(left.ParamSegs) - len(right.ParamSegs), nil
	}

	for i := 0; i < len(left.ParamSegs); i++ {
		if comp, err := cmpFcLit(left.ParamSegs[i], right.ParamSegs[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}
