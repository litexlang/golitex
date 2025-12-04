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
	if asAtom, ok := obj.(ast.Atom); ok {
		return atomObjString(asAtom)
	}
	if asFn, ok := obj.(*ast.FnObj); ok {
		return fnObjString(asFn)
	}
	return ""
}

func atomObjString(atomObj ast.Atom) string {
	if len(string(atomObj)) != 0 && '0' <= string(atomObj)[0] && string(atomObj)[0] <= '9' {
		return string(atomObj)
	} else if len(string(atomObj)) > 1 && string(atomObj)[0] == '-' && string(atomObj)[1] >= '0' && string(atomObj)[1] <= '9' {
		return fmt.Sprintf("(%s - %s)", "0", string(atomObj)[1:])
	}
	return fmt.Sprintf("{%s}", atomObj.String())
}

func fnObjString(fnObj *ast.FnObj) string {
	if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeySymbolPlus) {
		return fmt.Sprintf("(%s + %s)", ObjStringForParseAndExpandPolynomial(fnObj.Params[0]), ObjStringForParseAndExpandPolynomial(fnObj.Params[1]))
	}
	if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeySymbolStar) {
		return fmt.Sprintf("(%s * %s)", ObjStringForParseAndExpandPolynomial(fnObj.Params[0]), ObjStringForParseAndExpandPolynomial(fnObj.Params[1]))
	}
	if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeySymbolMinus) {
		if len(fnObj.Params) == 1 {
			return fmt.Sprintf("(%s - %s)", "0", ObjStringForParseAndExpandPolynomial(fnObj.Params[0]))
		} else if len(fnObj.Params) == 2 {
			return fmt.Sprintf("(%s - %s)", ObjStringForParseAndExpandPolynomial(fnObj.Params[0]), ObjStringForParseAndExpandPolynomial(fnObj.Params[1]))
		} else {
			panic("fnObjString: fnObj.ParamSegs has more than 2 elements")
		}
	}
	// 如果是幂运算，则把它展开成对应的乘法，比如(x+1)^2 展开成 (x+1) * (x+1)
	if ast.IsAtomObjAndEqualToStr(fnObj.FnHead, glob.KeySymbolPower) {
		base := ObjStringForParseAndExpandPolynomial(fnObj.Params[0])
		exp := ObjStringForParseAndExpandPolynomial(fnObj.Params[1])

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
		return fmt.Sprintf("{%s}", fnObj.String())
	}
	return fmt.Sprintf("{%s}", fnObj.String())
}
