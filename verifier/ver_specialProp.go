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

package litex_verifier

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) isCommutativeProp_BuiltinRule(stmt *ast.SpecFactStmt) bool {
	return ast.IsFcAtomWithNameAndEmptyPkg(&stmt.PropName, glob.KeySymbolEqual)
}

func (ver *Verifier) isCommutativeFn_BuiltinRule(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithNameAndEmptyPkg(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithNameAndEmptyPkg(&fnName, glob.KeySymbolStar) {
		return true
	}

	return false
}

func (ver *Verifier) isAssociativeFn_BuiltinRule(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithNameAndEmptyPkg(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithNameAndEmptyPkg(&fnName, glob.KeySymbolStar) {
		return true
	}

	return false
}
