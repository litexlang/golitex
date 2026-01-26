package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) matchPureFactWithOneInKnownUniFact(knownUniFact *ast.UniFactStmt, pureFactInKnownUniFact *ast.PureSpecificFactStmt, given *ast.PureSpecificFactStmt, state *VerState) *glob.VerRet {
	ok, uniMap := ver.matchParamsWithFreeParamsWithInstParamInPureFact(knownUniFact.Params, pureFactInKnownUniFact.Params, given.Params)

	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}

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

	nextState := NewVerState(2, false, true)
	for _, domFact := range knownUniFact.DomFacts {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.NewEmptyVerRetUnknown()
		}

		switch asInstDomFact := instDomFact.(type) {
		case ast.SpecificFactStmt:
			ret := ver.VerFactStmt(asInstDomFact, nextState)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		case *ast.OrStmt:
			ret := ver.VerFactStmt(instDomFact, nextState)
			if ret.IsNotTrue() {
				return glob.NewEmptyVerRetUnknown()
			}
		default:
			return glob.NewEmptyVerRetUnknown()
		}

	}

	return glob.NewVerRet(glob.StmtRetTypeTrue, given.String(), knownUniFact.Line, []string{knownUniFact.String()})
}
