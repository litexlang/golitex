package litex_verifier

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) isCommutativeProp(stmt *ast.SpecFactStmt) bool {
	if ast.IsFcAtomWithName(&stmt.PropName, glob.KeySymbolEqual) {
		return true
	}

	// TODO: 用mem来检查

	return false
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
