// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) haveObjWithSetParamsStPurePropStmtCheck(stmt *ast.HaveObjStWithParamSetsStmt, existStFact *ast.SpecFactStmt, state *VerState) *glob.StmtRet {
	ver := NewVerifier(exec.Env)

	for curEnvIndex := range exec.Env.EnvSlice {
		curEnv := &exec.Env.EnvSlice[curEnvIndex]
		knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(existStFact)
		if !got {
			continue
		}
		ret := ver.ExistStFactWithPureProp_FreeExistStFactMatchInstExistStFacts(stmt, existStFact, knownFacts, state)
		if ret.IsTrue() {
			return glob.NewStmtTrueWithStmt(stmt.String()).AddVerifyProcess(ret)
		}
	}

	for _, pkgEnvMgr := range exec.Env.EnvPkgMgr.AbsPkgPathEnvMgrMap {
		curEnv := pkgEnvMgr.EnvSlice[0]
		knownFacts, got := curEnv.KnownFactsStruct.SpecFactMem.GetSameEnumPkgPropFacts(existStFact)
		if !got {
			continue
		}
		ret := ver.ExistStFactWithPureProp_FreeExistStFactMatchInstExistStFacts(stmt, existStFact, knownFacts, state)
		if ret.IsTrue() {
			return glob.NewStmtTrueWithStmt(stmt.String()).AddVerifyProcess(ret)
		}
	}

	return glob.NewEmptyStmtUnknown()
}
