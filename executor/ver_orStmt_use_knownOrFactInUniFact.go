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
}
