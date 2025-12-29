package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) ExistStFactMatchRightInstExistStFact(freeExistStFact *ast.SpecFactStmt, instExistStFactToBeMatched *ast.SpecFactStmt, verState *VerState) *glob.VerMsg {
	freeExistParams, freeParams, freeSpecFact := freeExistStFact.TrueExistStFactToPropNameExistParamsParamsAndSpecFactAfterSt()
	rightExistParams, rightParams := instExistStFactToBeMatched.ExistStFactToPropNameExistParamsParams()

	if len(freeExistParams) != len(rightExistParams) || len(freeParams) != len(rightParams) {
		return nil
	}

	uniMap := map[string]ast.Obj{}
	for i, freeExistParam := range freeExistParams {
		uniMap[freeExistParam.String()] = rightExistParams[i]
	}

	instFreeSpecFact, err := freeSpecFact.Instantiate(uniMap)
	if err != nil {
		return nil
	}

	// 证明 inst Free Spec Fact 的每一个 param 等于 right 的 对应的 param
	for i, instFreeSpecFactParam := range instFreeSpecFact.(*ast.SpecFactStmt).Params {
		verRet := ver.VerFactStmt(ast.NewEqualFact(instFreeSpecFactParam, instExistStFactToBeMatched.Params[i]), verState)
		if verRet.IsNotTrue() {
			return nil
		}
	}

	return glob.NewVerMsg(freeExistStFact.String(), instExistStFactToBeMatched.Line, []string{instExistStFactToBeMatched.String()})
}
