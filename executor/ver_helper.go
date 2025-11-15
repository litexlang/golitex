// Copyright 2024 Jiachen Shen.
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
)

func (ver *Verifier) todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt *ast.SpecFactStmt) *env.Env {
	_ = stmt
	return nil
}

func (ver *Verifier) processOkMsg(state *VerState, msg string, verifiedBy string, args ...any) ExecRet {
	execRet := NewExecTrue(successVerString(msg, fmt.Sprintf(verifiedBy, args...)))
	if state.WithMsg {
		execRet = ver.successWithMsg(msg, fmt.Sprintf(verifiedBy, args...), execRet)
	}
	return execRet
}

func (ver *Verifier) paramsInSets(params []ast.Obj, sets []ast.Obj, state *VerState) ExecRet {
	if len(params) != len(sets) {
		return NewExecErr("params and sets length mismatch")
	}

	for i := range params {
		fact := ast.NewInFactWithFc(params[i], sets[i])
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return NewExecUnknown(ast.UnknownFactMsg(fact))
		}
	}
	return NewExecTrue("")
}

func (ver *Verifier) factsAreTrue(facts []ast.FactStmt, state *VerState) ExecRet {
	for _, fact := range facts {
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return NewExecUnknown(ast.UnknownFactMsg(fact))
		}
	}

	return NewExecTrue("")
}

func IsTrueOrErr(ok bool, err error) bool {
	return ok || err != nil
}

func IsFalseOrErr(ok bool, err error) bool {
	return !ok || err != nil
}
