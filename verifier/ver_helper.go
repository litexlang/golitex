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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt *ast.SpecFactStmt) *env.Env {
	_ = stmt
	return nil
}

func isErrOrOk(ok bool, err error) bool {
	return err != nil || ok
}

func (ver *Verifier) processOkMsg(state *VerState, msg string, verifiedBy string, args ...any) (bool, error) {
	if state.WithMsg {
		ver.successWithMsg(msg, fmt.Sprintf(verifiedBy, args...))
	}
	return true, nil
}

func (ver *Verifier) paramsInSets(params []ast.Fc, sets []ast.Fc, state *VerState) (bool, glob.Msgs, error) {
	if len(params) != len(sets) {
		return false, glob.Msgs{}, fmt.Errorf("params and sets length mismatch")
	}

	for i := range params {
		fact := ast.NewInFactWithFc(params[i], sets[i])
		ok, err := ver.VerFactStmt(fact, state)
		if err != nil {
			return false, glob.Msgs{}, err
		}
		if !ok {
			return false, glob.Msgs{ast.UnknownFactMsg(fact)}, nil
		}
	}
	return true, glob.Msgs{}, nil
}

func (ver *Verifier) factsAreTrue(facts []ast.FactStmt, state *VerState) (bool, glob.Msgs, error) {
	for _, fact := range facts {
		ok, err := ver.VerFactStmt(fact, state)
		if err != nil {
			return false, glob.Msgs{}, err
		}
		if !ok {
			return false, glob.Msgs{ast.UnknownFactMsg(fact)}, nil
		}
	}

	return true, glob.Msgs{}, nil
}

func VerFactInNewEnv(oldEnv *env.Env, facts []ast.FactStmt, state *VerState) (bool, error) {
	ver := NewVerifier(oldEnv)
	ver.newEnv(oldEnv)
	defer ver.deleteEnvAndRetainMsg()

	for _, fact := range facts {
		ok, err := ver.VerFactStmt(fact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
