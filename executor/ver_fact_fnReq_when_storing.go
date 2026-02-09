package litex_executor

import (
	ast "golitex/ast"
)

func (ver *Verifier) storeFactAndCheckFnReq(stmt ast.FactStmt) ast.VerRet {
	verRet := ver.VerFactStmt(stmt, Round0NoMsg())
	if verRet.IsNotTrue() {
		return verRet
	}

	ret := ver.Env.NewFact(stmt)
	if ret.IsNotTrue() {
		return ast.NewErrVerRet(stmt).AddExtraInfo(ret.String())
	}
	return ast.NewTrueVerRet(stmt, nil, "")
}
