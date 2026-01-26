package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) matchPureFactInKnownUniFactWithGiven(knownUniFact *ast.UniFactStmt, pureFactInKnownUniFact *ast.PureSpecificFactStmt, given *ast.PureSpecificFactStmt) *glob.VerRet {
	ok, _ := ver.matchParamsWithFreeParamsWithInstParam(knownUniFact.Params, pureFactInKnownUniFact.Params, given.Params)
	if ok {
		return glob.NewVerRet(glob.StmtRetTypeTrue, given.String(), knownUniFact.Line, []string{knownUniFact.String()})
	}
	return glob.NewEmptyVerRetUnknown()
}
