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

	return ver.matchFcInExistFactWithFreeParamsInForallFact(given, knownFact, verState)
}

func (ver *Verifier) matchFcInExistFactWithFreeParamsInForallFact(given *ast.ExistSpecificFactStmt, knownFact env.KnownSpecFact_InUniFact, verState *VerState) *glob.VerRet {
	usedNames := map[string]struct{}{}
	for _, param := range knownFact.UniFact.Params {
		usedNames[string(param)] = struct{}{}
	}

	newExistFreeParams := ver.Env.GenerateNoDuplicateNames(len(given.ExistFreeParams), usedNames)

	newGiven, err := given.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, given.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	newKnown, err := knownFact.SpecFact.(*ast.ExistSpecificFactStmt).ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, knownFact.String(), glob.BuiltinLine0, []string{err.Error()})
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

	ok, uniConMap, err := ver.matchUniFactParamsWithSpecFactParams(knownFcs, knownFact.UniFact.Params, givenFcs)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, knownFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	if !ok {
		return glob.NewEmptyVerRetUnknown()
	}
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, knownFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	instKnownFact, err := newKnown.Instantiate(uniConMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, knownFact.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	// 每一位都一样
	for i := range instKnownFact.(*ast.ExistSpecificFactStmt).ExistFreeParamSets {
		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(instKnownFact.(*ast.ExistSpecificFactStmt).ExistFreeParamSets[i], given.ExistFreeParamSets[i]), FinalRoundNoMsg().CopyAndReqOkToTrue())
		if verRet.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}
	}
	for i := range instKnownFact.(*ast.ExistSpecificFactStmt).PureFact.Params {
		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(instKnownFact.(*ast.ExistSpecificFactStmt).PureFact.Params[i], given.PureFact.Params[i]), FinalRoundNoMsg().CopyAndReqOkToTrue())
		if verRet.IsNotTrue() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewEmptyVerRetTrue()
}
