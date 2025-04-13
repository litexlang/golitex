/*
 * Copyright 2024 Jiachen Shen.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
 * Visit litexlang.org and https://github.com/litexlang/golitex for more information.
 */

package litex_comparator

import (
	"fmt"
	ast "golitex/litex_ast"
	mem "golitex/litex_memory"
)

func EqualFactMemoryTreeNodeCompare(left, right *mem.EqualFactMemoryTreeNode) (int, error) {
	return cmpFcLit(left.FcAsKey, right.FcAsKey)
}

// 注：像1+1=2这种字面量的比较，我在这里不比。我是比完完全全一样的
func cmpFcLit(left, right ast.Fc) (int, error) {
	typeComp, fcEnum, err := ast.CmpFcType(left, right)
	if typeComp != 0 || err != nil {
		return typeComp, err
	}

	if fcEnum == ast.FcAtomEnum {
		return cmpFcAtomLit(left.(*ast.FcAtom), right.(*ast.FcAtom))
	} else if fcEnum == ast.FcFnEnum {
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

	if len(left.Value) != len(right.Value) {
		return len(left.Value) - len(right.Value), nil
	}

	for i := 0; i < len(left.Value); i++ {
		if left.Value[i] != right.Value[i] {
			return int(left.Value[i]) - int(right.Value[i]), nil
		}
	}

	return 0, nil
}

func cmpFcFnLit(left, right *ast.FcFn) (int, error) {
	if comp, err := cmpFcAtomLit(&left.FnHead, &right.FnHead); comp != 0 || err != nil {
		return comp, err
	}

	if len(left.ParamSegs) != len(right.ParamSegs) {
		return len(left.ParamSegs) - len(right.ParamSegs), nil
	}

	for i := 0; i < len(left.ParamSegs); i++ {
		if comp, err := cmpFcFnSegLit(left.ParamSegs[i], right.ParamSegs[i]); comp != 0 || err != nil {
			return comp, err
		}
	}

	return 0, nil
}

func cmpFcFnSegLit(left, right *ast.FcFnSeg) (int, error) {
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
