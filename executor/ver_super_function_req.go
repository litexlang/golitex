package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verSuperFunctionReq(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	switch stmt.PropName {
	case glob.KeywordUnion:
		return ver.verUnionReq(stmt, state)
	case glob.KeywordIntersect:
		return ver.verIntersectReq(stmt, state)
	default:
		return glob.ErrRet(fmt.Sprintf("unknown super function: %s", stmt.PropName))
	}
}

func (ver *Verifier) verUnionReq(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("union expects 2 parameters, got %d", len(stmt.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}

func (ver *Verifier) verIntersectReq(stmt *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	if len(stmt.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("intersect expects 2 parameters, got %d", len(stmt.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}
