package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) verEqualsFactStmt(stmt *ast.EqualsFactStmt, state VerState) (bool, error) {
	return true, nil
}
