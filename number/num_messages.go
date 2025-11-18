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

package litex_num

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
	"strings"
)

func ObjStringForParseAndExpandPolynomial(obj ast.Obj) string {
	if asAtom, ok := obj.(ast.AtomObj); ok {
		return atomObjString(asAtom)
	}
	if asFn, ok := obj.(*ast.FnObj); ok {
		return fnObjString(asFn)
	}
	return ""
}

func atomObjString(objAtom ast.AtomObj) string {
	if len(string(objAtom)) != 0 && '0' <= string(objAtom)[0] && string(objAtom)[0] <= '9' {
		return string(objAtom)
	} else if len(string(objAtom)) > 1 && string(objAtom)[0] == '-' && string(objAtom)[1] >= '0' && string(objAtom)[1] <= '9' {
		return fmt.Sprintf("(%s - %s)", "0", string(objAtom)[1:])
	}
	return fmt.Sprintf("{%s}", objAtom.String())
}

func fnObjString(objFn *ast.FnObj) string {
	if ast.IsAtomObjAndEqualToStr(objFn.FnHead, glob.KeySymbolPlus) {
		return fmt.Sprintf("(%s + %s)", ObjStringForParseAndExpandPolynomial(objFn.Params[0]), ObjStringForParseAndExpandPolynomial(objFn.Params[1]))
	}
	if ast.IsAtomObjAndEqualToStr(objFn.FnHead, glob.KeySymbolStar) {
		return fmt.Sprintf("(%s * %s)", ObjStringForParseAndExpandPolynomial(objFn.Params[0]), ObjStringForParseAndExpandPolynomial(objFn.Params[1]))
	}
	if ast.IsAtomObjAndEqualToStr(objFn.FnHead, glob.KeySymbolMinus) {
		if len(objFn.Params) == 1 {
			return fmt.Sprintf("(%s - %s)", "0", ObjStringForParseAndExpandPolynomial(objFn.Params[0]))
		} else if len(objFn.Params) == 2 {
			return fmt.Sprintf("(%s - %s)", ObjStringForParseAndExpandPolynomial(objFn.Params[0]), ObjStringForParseAndExpandPolynomial(objFn.Params[1]))
		} else {
			panic("fnObjString: objFn.ParamSegs has more than 2 elements")
		}
	}
	// 如果是幂运算，则把它展开成对应的乘法，比如(x+1)^2 展开成 (x+1) * (x+1)
	if ast.IsAtomObjAndEqualToStr(objFn.FnHead, glob.KeySymbolPower) {
		base := ObjStringForParseAndExpandPolynomial(objFn.Params[0])
		exp := ObjStringForParseAndExpandPolynomial(objFn.Params[1])

		// Try to parse exponent as integer
		if expInt, err := strconv.Atoi(exp); err == nil {
			if expInt == 0 {
				return "1"
			}
			if expInt > 0 {
				// For positive integers, expand into multiplication
				terms := make([]string, expInt)
				for i := 0; i < expInt; i++ {
					terms[i] = base
				}
				return fmt.Sprintf("(%s)", strings.Join(terms, " * "))
			}
		}
		// For non-integer or negative exponents, keep original form
		// return "(" + base + "^" + exp + ")"
		return fmt.Sprintf("{%s}", objFn.String())
	}
	return fmt.Sprintf("{%s}", objFn.String())
}
