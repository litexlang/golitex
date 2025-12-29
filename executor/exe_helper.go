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
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func notOkExec(state *glob.StmtRet, err error) bool {
	if err != nil {
		return true
	}
	if state.IsUnknown() || state.IsErr() {
		return true
	}
	return false
}

func (exec *Executor) NewCommutativeProp(specFact *ast.SpecFactStmt) {
	if _, ok := exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)]; !ok {
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)] = env.NewCommutativePropMemItemStruct()
	}

	switch specFact.FactType {
	case ast.TruePure:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].TruePureIsCommutative = true
	case ast.FalsePure:
		exec.Env.CurEnv().CommutativePropMem[string(specFact.PropName)].FalsePureIsCommutative = true
	default:
		panic("not implemented: not commutative prop")
	}
}

func (exec *Executor) verifyFactsAtCurEnv(proofs []ast.FactStmt, verState *VerState) (*glob.StmtRet, ast.Stmt, error) {
	ver := NewVerifier(exec.Env)
	for _, proof := range proofs {
		verRet := ver.VerFactStmt(proof, verState)
		if verRet.IsErr() {
			return glob.NewEmptyStmtError(), proof, fmt.Errorf(verRet.String())
		} else if verRet.IsUnknown() {
			return glob.NewEmptyStmtUnknown(), proof, nil
		}

		ret := exec.Env.NewFactWithoutCheckingNameDefined(proof)
		if ret.IsErr() {
			return glob.ErrRet(ret.String()), proof, fmt.Errorf(ret.String())
		}
	}
	return glob.NewEmptyStmtTrue(), nil, nil
}

func (exec *Executor) GetBuiltinEnv() *env.EnvMemory {
	return exec.Env.GetUpMostEnv()
}

func (exec *Executor) GetSecondUpMostEnv() *env.EnvMemory {
	return exec.Env.GetSecondUpMostEnv()
}
