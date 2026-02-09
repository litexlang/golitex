package litex_executor

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) checkFnReqInsideFact(originalFact ast.FactStmt, state *VerState) ast.VerRet {
	switch fact := originalFact.(type) {
	case *ast.PureSpecificFactStmt:
		return ver.checkFnReqInsidePureSpecificFactStmt(fact, state)
	case *ast.ExistSpecificFactStmt:
		return ver.checkFnReqInsideExistSpecificFactStmt(fact, state)
	case *ast.OrStmt:
		return ver.checkFnReqInsideOrStmt(fact, state)
	case *ast.UniFactStmt:
		return ver.checkFnReqInsideUniFactStmt(fact, state)
	default:
		return ast.NewErrVerRet(originalFact).AddExtraInfo(fmt.Sprintf("unexpected fact statement: %s", originalFact.String()))
	}
}

func (ver *Verifier) checkFnReqInsidePureSpecificFactStmt(fact *ast.PureSpecificFactStmt, state *VerState) ast.VerRet {
	stateNoMsg := state.GetNoMsg()
	for _, param := range fact.Params {
		verRet := ver.objSatisfyFnReq(param, stateNoMsg)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}
	}

	return ast.NewTrueVerRet(fact, nil, "")
}

func (ver *Verifier) checkFnReqInsideExistSpecificFactStmt(fact *ast.ExistSpecificFactStmt, state *VerState) ast.VerRet {
	// TODO: 这里检查 exist 的方式大概率有问题
	ret := ver.Env.LookUpNamesInFact(fact, map[string]struct{}{})
	if ret.IsErr() {
		return ast.NewErrVerRet(fact).AddExtraInfos(ret.GetMsg())
	}
	if ret.IsUnknown() {
		return ast.NewUnknownVerRet(fact).AddExtraInfos(ret.GetMsg())
	}
	return ast.NewTrueVerRet(fact, nil, "")
}

func (ver *Verifier) checkFnReqInsideOrStmt(fact *ast.OrStmt, state *VerState) ast.VerRet {
	for _, fact := range fact.Facts {
		verRet := ver.checkFnReqInsideFact(fact, state)
		if verRet.IsNotTrue() {
			return verRet
		}
	}

	return ast.NewTrueVerRet(fact, nil, "")
}

func (ver *Verifier) checkFnReqInsideUniFactStmt(fact *ast.UniFactStmt, state *VerState) ast.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	newFact, err := ver.replaceUniFactParamsWithRandomParams(fact)
	if err != nil {
		return ast.NewErrVerRet(fact).AddExtraInfo(err.Error())
	}

	declareRet := ver.declareParamsInUniFactAndCheckFnReqOfParamSetsAndDoms(newFact, state)
	if declareRet.IsNotTrue() {
		return ast.NewErrVerRet(fact).AddExtraInfo(declareRet.String())
	}

	// check thens
	verRet := ver.checkFnReqInsideReversibleFacts(newFact.ThenFacts, state)
	if verRet.IsNotTrue() {
		return ast.NewErrVerRet(fact).AddExtraInfo(verRet.String())
	}

	return ast.NewTrueVerRet(fact, nil, "")
}

func (ver *Verifier) checkFnReqOfObj(param ast.Obj, state *VerState) ast.VerRet {
	return ver.objSatisfyFnReq(param, state)
}

func (ver *Verifier) checkFnReqInsideObjs(paramSets ast.ObjSlice, state *VerState) ast.VerRet {
	for _, paramSet := range paramSets {
		verRet := ver.objSatisfyFnReq(paramSet, state)
		if verRet.IsNotTrue() {
			return verRet.AddExtraInfo(fmt.Sprintf("parameter set %s does not satisfy function requirement", paramSet.String()))
		}
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) checkFnReqInsideReversibleFacts(domFacts ast.ReversibleFacts, state *VerState) ast.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	for _, domFact := range domFacts {
		verRet := ver.checkFnReqInsideFact(domFact, state)
		if verRet.IsNotTrue() {
			return verRet
		}

		ret := ver.Env.NewFact(domFact)
		if ret.IsNotTrue() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
		}
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (ver *Verifier) checkFnReqInsideFacts(iffFacts ast.FactStmtSlice, state *VerState) ast.VerRet {

	ver.newEnv()
	defer ver.deleteEnv()

	for _, iffFact := range iffFacts {
		verRet := ver.checkFnReqInsideFact(iffFact, state)
		if verRet.IsNotTrue() {
			return verRet
		}

		// prop p(x R): x != 0, x / x = 1. 这里如果不能 new fact，那 x / x 的fn req验证就不行了
		ret := ver.Env.NewFact(iffFact)
		if ret.IsNotTrue() {
			return ast.NewErrVerRet(nil).AddExtraInfo(ret.String())
		}
	}
	return ast.NewTrueVerRet(nil, nil, "")
}

func (exec *Executor) checkFnReqInsideDefProp(stmt *ast.DefPropStmt, state *VerState) ast.VerRet {
	exec.NewEnv()
	defer exec.deleteEnv()

	ver := NewVerifier(exec.Env)
	var err error

	stmt, err = ver.replaceParamsInDefPropWithRandomParams(stmt)
	if err != nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(err.Error()).AddExtraInfo(stmt.String())
	}

	// declare params in def prop and check fn req of param sets
	verRet := ver.declareParamsInDefPropAndCheckFnReqOfParamSets(stmt, state)
	if verRet.IsNotTrue() {
		return verRet
	}

	// check fn req of param sets
	verRet = ver.checkFnReqInsideObjs(stmt.DefHeader.ParamSets, state)
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
