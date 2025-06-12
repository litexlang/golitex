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

package litex_num

import (
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
	"strings"
)

func FcStringForParseAndExpandPolynomial(fc ast.Fc) string {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		return fcAtomString(asAtom)
	}
	if asFn, ok := fc.(*ast.FcFn); ok {
		return fcFnString(asFn)
	}
	return ""
}

func fcAtomString(fcAtom *ast.FcAtom) string {
	if len(fcAtom.Name) != 0 && '0' <= fcAtom.Name[0] && fcAtom.Name[0] <= '9' {
		return fcAtom.Name
	}
	return "[" + fcAtom.String() + "]"
}

func fcFnString(fcFn *ast.FcFn) string {
	if ast.IsFcAtomWithNameAndEmptyPkg(fcFn.FnHead, glob.KeySymbolPlus) {
		return "(" + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[0]) + " + " + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[1]) + ")"
	}
	if ast.IsFcAtomWithNameAndEmptyPkg(fcFn.FnHead, glob.KeySymbolStar) {
		return "(" + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[0]) + " * " + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[1]) + ")"
	}
	if ast.IsFcAtomWithNameAndEmptyPkg(fcFn.FnHead, glob.KeySymbolMinus) {
		if len(fcFn.ParamSegs) == 1 {
			return "(" + "0" + " - " + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[0]) + ")"
		} else if len(fcFn.ParamSegs) == 2 {
			return "(" + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[0]) + " - " + FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[1]) + ")"
		} else {
			panic("fcFnString: fcFn.ParamSegs has more than 2 elements")
		}
	}
	if ast.IsFcAtomWithNameAndEmptyPkg(fcFn.FnHead, glob.KeySymbolPower) {
		base := FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[0])
		exp := FcStringForParseAndExpandPolynomial(fcFn.ParamSegs[1])

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
				return "(" + strings.Join(terms, " * ") + ")"
			}
		}
		// For non-integer or negative exponents, keep original form
		return "(" + base + "^" + exp + ")"
	}
	return "[" + fcFn.String() + "]"
}
