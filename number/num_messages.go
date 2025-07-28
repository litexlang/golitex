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

package litex_num

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
	"strings"
)

func FcStringForParseAndExpandPolynomial(fc ast.Fc) string {
	if asAtom, ok := fc.(ast.FcAtom); ok {
		return fcAtomString(asAtom)
	}
	if asFn, ok := fc.(*ast.FcFn); ok {
		return fcFnString(asFn)
	}
	return ""
}

func fcAtomString(fcAtom ast.FcAtom) string {
	if len(string(fcAtom)) != 0 && '0' <= string(fcAtom)[0] && string(fcAtom)[0] <= '9' {
		return string(fcAtom)
	} else if len(string(fcAtom)) > 1 && string(fcAtom)[0] == '-' && string(fcAtom)[1] >= '0' && string(fcAtom)[1] <= '9' {
		return fmt.Sprintf("(%s - %s)", "0", string(fcAtom)[1:])
	}
	return fmt.Sprintf("{%s}", fcAtom.String())
}

func fcFnString(fcFn *ast.FcFn) string {
	if ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.KeySymbolPlus) {
		return fmt.Sprintf("(%s + %s)", FcStringForParseAndExpandPolynomial(fcFn.Params[0]), FcStringForParseAndExpandPolynomial(fcFn.Params[1]))
	}
	if ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.KeySymbolStar) {
		return fmt.Sprintf("(%s * %s)", FcStringForParseAndExpandPolynomial(fcFn.Params[0]), FcStringForParseAndExpandPolynomial(fcFn.Params[1]))
	}
	if ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.KeySymbolMinus) {
		if len(fcFn.Params) == 1 {
			return fmt.Sprintf("(%s - %s)", "0", FcStringForParseAndExpandPolynomial(fcFn.Params[0]))
		} else if len(fcFn.Params) == 2 {
			return fmt.Sprintf("(%s - %s)", FcStringForParseAndExpandPolynomial(fcFn.Params[0]), FcStringForParseAndExpandPolynomial(fcFn.Params[1]))
		} else {
			panic("fcFnString: fcFn.ParamSegs has more than 2 elements")
		}
	}
	// 如果是幂运算，则把它展开成对应的乘法，比如(x+1)^2 展开成 (x+1) * (x+1)
	if ast.IsFcAtomAndEqualToStr(fcFn.FnHead, glob.KeySymbolPower) {
		base := FcStringForParseAndExpandPolynomial(fcFn.Params[0])
		exp := FcStringForParseAndExpandPolynomial(fcFn.Params[1])

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
		return fmt.Sprintf("{%s}", fcFn.String())
	}
	return fmt.Sprintf("{%s}", fcFn.String())
}
