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

			// switch asFact := instDomFact.(type) {
			// case ast.SpecificFactStmt:
			// 	nextState := NewVerState(2, false, true)
			// 	ret := ver.VerFactStmt(asFact, nextState)
			// 	if ret.IsNotTrue() {
			// 		return glob.NewEmptyVerRetUnknown()
			// 	}
			// default:
			// 	ret := ver.VerFactStmt(asFact, state)
			// 	if ret.IsNotTrue() {
			// 		return glob.NewEmptyVerRetUnknown()
			// 	}
			// }

			if asPureFact, ok := instDomFact.(*ast.PureSpecificFactStmt); ok {
				if asPureFact.PropName == glob.KeySymbolEqual {
					// nextState := state.GetFinalRound()
					nextState := NewVerState(2, false, true)
					ret := ver.VerFactStmt(instDomFact, nextState)
					if ret.IsNotTrue() {
						return glob.NewEmptyVerRetUnknown()
					}
				}
			} else {
				ret := ver.VerFactStmt(instDomFact, state)
				if ret.IsNotTrue() {
					return glob.NewEmptyVerRetUnknown()
				}
			}
		}

		return glob.NewVerRet(glob.StmtRetTypeTrue, given.String(), knownUniFact.Line, []string{knownUniFact.String()})
	}

	return glob.NewEmptyVerRetUnknown()
}
