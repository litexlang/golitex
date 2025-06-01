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

package litex_verifier

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) isCommutativeProp(stmt *ast.SpecFactStmt) bool {
	return ast.IsFcAtomWithName(&stmt.PropName, glob.KeySymbolEqual)

	// TODO: 用mem来检查

}

func (ver *Verifier) isCommutativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolStar) {
		return true
	}

	// TODO: 用 specMem 来检查

	return false
}

func (ver *Verifier) isAssociativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolStar) {
		return true
	}

	// TODO: 用 specMem 来检查

	return false
}
