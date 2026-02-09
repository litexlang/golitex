package litex_executor

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) checkFnReqInsideParamSets(paramSets ast.ObjSlice, state *VerState) ast.VerRet {
	for _, paramSet := range paramSets {
		verRet := ver.objSatisfyFnReq(paramSet, state)
		if verRet.IsNotTrue() {
			return verRet.AddExtraInfo(fmt.Sprintf("parameter set %s does not satisfy function requirement", paramSet.String()))
		}
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) checkFnReqInsideReversibleFacts(domFacts ast.ReversibleFacts, state *VerState) ast.VerRet {
	panic("")
}

func (ver *Verifier) checkFnReqInsideFacts(iffFacts ast.FactStmtSlice, state *VerState) ast.VerRet {
	panic("not implemented")
}

func (exec *Executor) checkFnReqInsideDefProp(stmt *ast.DefPropStmt, state *VerState) ast.VerRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	ver := NewVerifier(exec.Env)

	// check fn req of param sets
	verRet := ver.checkFnReqInsideParamSets(stmt.DefHeader.ParamSets, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// check fn req of iff facts
	verRet = ver.checkFnReqInsideFacts(stmt.IffFactsOrNil, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// check fn req of implication facts
	verRet = ver.checkFnReqInsideReversibleFacts(stmt.ImplicationFactsOrNil, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	return ast.NewTrueVerRet(nil, nil, "")
}
