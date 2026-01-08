package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (exec *Executor) implyStmt(stmt *ast.ImplyStmt) *glob.StmtRet {
	ver := NewVerifier(exec.Env)

	// 检查涉及到的函数都OK了
	for _, domFact := range stmt.DomFacts {
		switch domFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.checkFnsReq(domFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret.ToStmtRet()
			}
		case *ast.OrStmt:
			panic("")
		}
	}

	for _, ifFact := range stmt.IfFacts {
		switch ifFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.checkFnsReq(ifFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret.ToStmtRet()
			}
		case *ast.OrStmt:
			panic("")
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		switch thenFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.checkFnsReq(thenFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret.ToStmtRet()
			}
		case *ast.OrStmt:
			panic("")
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		switch thenFact.(type) {
		case *ast.SpecFactStmt:
			ret := ver.proveOneThenFactInImplyStmt(stmt, thenFact.(*ast.SpecFactStmt), Round0Msg())
			if ret.IsNotTrue() {
				return ret
			}
		case *ast.OrStmt:
			panic("")
		}
	}
	return exec.NewTrueStmtRet(stmt)
}

func (ver *Verifier) proveOneThenFactInImplyStmt(stmt *ast.ImplyStmt, thenFact *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	for curEnvIndex := range ver.Env.EnvSlice {
		curEnv := &ver.Env.EnvSlice[curEnvIndex]
		verRet := ver.specFact_ImplyMem_atCurEnv(curEnv, stmt, thenFact, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet.ToStmtRet()
		}
	}

	curEnv := env.BuiltinEnvMgrWithEmptyEnvPkgMgr.CurEnv()
	verRet := ver.specFact_ImplyMem_atCurEnv(curEnv, stmt, thenFact, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet.ToStmtRet()
	}

	for _, pkgEnvMgr := range ver.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		verRet := ver.specFact_ImplyMem_atCurEnv(&curEnv, stmt, thenFact, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet.ToStmtRet()
		}
	}

	return glob.NewEmptyVerRetUnknown().ToStmtRet()
}

func (ver *Verifier) specFact_ImplyMem_atCurEnv(curEnv *env.EnvMemory, stmt *ast.ImplyStmt, fact *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		return glob.NewVerMsg2(glob.StmtRetTypeUnknown, stmt.String(), stmt.GetLine(), []string{fmt.Sprintf("specFact_UniMem_atCurEnv: state is %s", state)})
	}

	searchedSpecFacts, got := curEnv.KnownFactsStruct.SpecFactInImplyTemplateMem.GetSameEnumPkgPropFacts(fact)

	if !got {
		return glob.NewEmptyVerRetUnknown()
	}

	_ = searchedSpecFacts
	panic("")
}
