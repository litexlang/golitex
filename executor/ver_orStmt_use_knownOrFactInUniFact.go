package litex_executor

import (
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) verOrStmt_UseOrInUniFactMem(stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(curEnv, stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.orFact_UseOrInUniFactMem_atCurEnv(&curEnv, stmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) orFact_UseOrInUniFactMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.OrStmt, state *VerState) *glob.VerRet {
	knownOrFacts, got := curEnv.OrFactInUniFactMem[string(stmt.Facts[0].GetPropName())]
	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	for _, knownOrFactInUniFact := range knownOrFacts {
		ret := ver.useKnownOrFactInUniFactToCheckGivenOrFact(stmt, knownOrFactInUniFact, state)
		if ret.IsTrue() || ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) useKnownOrFactInUniFactToCheckGivenOrFact(given *ast.OrStmt, knownOrFactInUni *env.OrFactInUniFact, state *VerState) *glob.VerRet {
	if len(given.Facts) != len(knownOrFactInUni.OrFact.Facts) {
		return glob.NewEmptyVerRetUnknown()
	}

	for i := range given.Facts {
		if given.Facts[i].String() != knownOrFactInUni.OrFact.Facts[i].String() || given.Facts[i].GetFactType() != knownOrFactInUni.OrFact.Facts[i].GetFactType() {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	return glob.NewEmptyVerRetTrue()
}
