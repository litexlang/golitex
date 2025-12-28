package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verSuperFunctionReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	switch fnObj.FnHead.String() {
	case glob.KeywordUnion:
		return ver.verUnionReq(fnObj, state)
	case glob.KeywordIntersect:
		return ver.verIntersectReq(fnObj, state)
	default:
		return glob.ErrRet(fmt.Sprintf("unknown super function: %s", fnObj.FnHead))
	}
}

func (ver *Verifier) verUnionReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	if len(fnObj.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("union expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}

func (ver *Verifier) verIntersectReq(fnObj *ast.FnObj, state *VerState) *glob.StmtRet {
	if len(fnObj.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("intersect expects 2 parameters, got %d", len(fnObj.Params)))
	}

	_ = state

	return glob.NewEmptyStmtTrue()
}
