// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_num

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func FcString(fc ast.Fc) string {
	if asAtom, ok := fc.(*ast.FcAtom); ok {
		return fcAtomString(asAtom)
	}
	if asFn, ok := fc.(*ast.FcFn); ok {
		return fcFnString(asFn)
	}
	return ""
}

func fcAtomString(fcAtom *ast.FcAtom) string {
	if len(fcAtom.Name) != 0 && 0 <= fcAtom.Name[0] && fcAtom.Name[0] <= '9' {
		return fcAtom.Name
	}
	return "[" + fcAtom.String() + "]"
}

func fcFnString(fcFn *ast.FcFn) string {
	if ast.IsFcAtomWithName(fcFn.FnHead, glob.KeySymbolPlus) {
		return "(" + FcString(fcFn.ParamSegs[0]) + " + " + FcString(fcFn.ParamSegs[1]) + ")"
	}
	if ast.IsFcAtomWithName(fcFn.FnHead, glob.KeySymbolStar) {
		return "(" + FcString(fcFn.ParamSegs[0]) + " * " + FcString(fcFn.ParamSegs[1]) + ")"
	}
	if ast.IsFcAtomWithName(fcFn.FnHead, glob.KeySymbolMinus) {
		return "(" + FcString(fcFn.ParamSegs[0]) + " - " + FcString(fcFn.ParamSegs[1]) + ")"
	}
	return "[" + fcFn.String() + "]"
}
