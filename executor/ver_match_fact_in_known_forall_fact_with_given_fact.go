package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) matchPureFactInKnownUniFactWithGiven(knownUniFact *ast.UniFactStmt, pureFactInKnownUniFact *ast.PureSpecificFactStmt, given *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	ok, uniMap := ver.matchParamsWithFreeParamsWithInstParam(knownUniFact.Params, pureFactInKnownUniFact.Params, given.Params)

	if ok {
		for i, paramSet := range knownUniFact.ParamSets {
			instParamSet, err := paramSet.Instantiate(uniMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}
			inFact := ast.NewInFactWithObj(uniMap[knownUniFact.Params[i]], instParamSet)
			ret := ver.VerFactStmt(inFact, state)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		for _, domFact := range knownUniFact.DomFacts {
			instDomFact, err := domFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}
			ret := ver.VerFactStmt(instDomFact, state)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		}

		return glob.NewVerRet(glob.StmtRetTypeTrue, given.String(), knownUniFact.Line, []string{knownUniFact.String()})
	}

	return glob.NewEmptyVerRetUnknown()
}
