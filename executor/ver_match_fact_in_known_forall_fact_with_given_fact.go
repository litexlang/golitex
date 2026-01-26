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

		nextState := NewVerState(2, false, true)
		for _, domFact := range knownUniFact.DomFacts {
			instDomFact, err := domFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewEmptyVerRetUnknown()
			}

			// warning : 这里不应该需要分类处理。因为我的equal在什么地方有bug，所以要有额外的对equal的不同的处理。不分类会让 forall x Z: (7 * x + 1) % 7 = ((7 * x) % 7 + 1 % 7) % 7 = (0 + 1) % 7 = 1 不能通过
			// TODO
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

	return glob.NewEmptyVerRetUnknown()
}
