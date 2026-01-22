package litex_executor

import (
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) MatchExistFactUseForallMemory(given *ast.ExistSpecificFactStmt, knownFacts []env.KnownSpecFact_InUniFact, verState *VerState) *glob.VerRet {
LoopOverFacts:
	for _, knownFact := range knownFacts {
		verRet := ver.MatchExistSpecificFactWithExistSpecFactInUniFact(given, knownFact, verState)
		if verRet.IsErr() {
			return glob.NewVerMsg(glob.StmtRetTypeError, given.String(), glob.BuiltinLine0, []string{verRet.String()})
		}
		if verRet.IsUnknown() {
			continue LoopOverFacts
		}
		if verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) MatchExistSpecificFactWithExistSpecFactInUniFact(given *ast.ExistSpecificFactStmt, knownFact env.KnownSpecFact_InUniFact, verState *VerState) *glob.VerRet {
	stored := knownFact.SpecFact.(*ast.ExistSpecificFactStmt)

	if len(stored.ExistFreeParams) != len(given.ExistFreeParams) {
		return glob.NewEmptyVerRetUnknown()
	}

	if given.IsTrue != stored.IsTrue {
		return glob.NewEmptyVerRetUnknown()
	}

	if given.PureFact.IsTrue != stored.PureFact.IsTrue {
		return glob.NewEmptyVerRetUnknown()
	}

	uniMap, verRet := ver.matchFcInExistFactWithFreeParamsInForallFact(given, knownFact.UniFact.Params, knownFact.SpecFact.(*ast.ExistSpecificFactStmt), verState)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	ver.newEnv()
	defer ver.deleteEnv()

	for i, paramSet := range knownFact.UniFact.ParamSets {
		instParamSet, err := paramSet.Instantiate(uniMap)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, knownFact.String(), glob.BuiltinLine0, []string{err.Error()})
		}
		verRet := ver.VerFactStmt(ast.NewInFactWithObj(uniMap[string(knownFact.UniFact.Params[i])], instParamSet), verState)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
		}
	}

	// 证明所有的dom和dom都成立
	for _, domFact := range knownFact.UniFact.DomFacts {
		verRet := ver.VerFactStmt(domFact, verState)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) matchFcInExistFactWithFreeParamsInForallFact(given *ast.ExistSpecificFactStmt, freeParams []string, knownExistFactInUniFact *ast.ExistSpecificFactStmt, verState *VerState) (map[string]ast.Obj, *glob.VerRet) {
	usedNames := map[string]struct{}{}
	for _, param := range freeParams {
		usedNames[string(param)] = struct{}{}
	}

	newExistFreeParams := ver.Env.GenerateNoDuplicateNames(len(given.ExistFreeParams), usedNames)

	newGiven, err := given.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return nil, glob.NewVerMsg(glob.StmtRetTypeError, given.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	newKnown, err := knownExistFactInUniFact.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return nil, glob.NewVerMsg(glob.StmtRetTypeError, knownExistFactInUniFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	givenFcs := []ast.Obj{}
	for _, paramSet := range newGiven.ExistFreeParamSets {
		givenFcs = append(givenFcs, paramSet)
	}
	for _, param := range newGiven.PureFact.Params {
		givenFcs = append(givenFcs, param)
	}

	knownFcs := []ast.Obj{}
	for _, paramSet := range newKnown.ExistFreeParamSets {
		knownFcs = append(knownFcs, paramSet)
	}
	for _, param := range newKnown.PureFact.Params {
		knownFcs = append(knownFcs, param)
	}

	ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(knownFcs, freeParams, givenFcs)
	if err != nil {
		return nil, glob.NewVerMsg(glob.StmtRetTypeError, knownExistFactInUniFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if !ok {
		return nil, glob.NewEmptyVerRetUnknown()
	}
	if err != nil {
		return nil, glob.NewVerMsg(glob.StmtRetTypeError, knownExistFactInUniFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	instKnownFact, err := newKnown.Instantiate(uniConMap)
	if err != nil {
		return nil, glob.NewVerMsg(glob.StmtRetTypeError, knownExistFactInUniFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if instKnownFact.String() == given.String() {
		return nil, glob.NewEmptyVerRetTrue()
	}

	return uniConMap, glob.NewEmptyVerRetTrue()
}

func GetParamsFromExistFactForMatchUniFactParams(given *ast.ExistSpecificFactStmt, knownExistFactInUniFact *ast.ExistSpecificFactStmt) {

}
