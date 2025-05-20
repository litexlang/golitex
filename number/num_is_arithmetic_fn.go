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

func isAdd(stmt *ast.FcFn) bool {
	asAtom, ok := stmt.FnHead.(*ast.FcAtom)
	if !ok {
		return false
	}
	if asAtom.Name == glob.KeySymbolPlus {
		return len(stmt.ParamSegs) == 2
	}
	return false
}

func isMul(stmt *ast.FcFn) bool {
	asAtom, ok := stmt.FnHead.(*ast.FcAtom)
	if !ok {
		return false
	}
	if asAtom.Name == glob.KeySymbolStar {
		return len(stmt.ParamSegs) == 2
	}
	return false
}

func isMinusAsInfix(stmt *ast.FcFn) bool {
	asAtom, ok := stmt.FnHead.(*ast.FcAtom)
	if !ok {
		return false
	}
	if asAtom.Name == glob.KeySymbolMinus {
		return len(stmt.ParamSegs) == 2
	}
	return false
}

func isMinusAsPrefix(stmt *ast.FcFn) bool {
	asAtom, ok := stmt.FnHead.(*ast.FcAtom)
	if !ok {
		return false
	}
	if asAtom.Name == glob.KeySymbolMinus {
		return len(stmt.ParamSegs) == 1
	}
	return false
}
