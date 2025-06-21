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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) verUniFactWithIff(stmt *ast.UniFactWithIffStmt, state VerState) (bool, error) {
	ok, err := ver.uniFactWithIff_CheckThenToIff(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.uniFactWithIff_CheckIffToThen(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIff_CheckThenToIff(stmt *ast.UniFactWithIffStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.UniFact.ThenFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.IffFacts {
		ok, err := ver.VerFactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.newMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFact(toCheckFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIff_CheckIffToThen(stmt *ast.UniFactWithIffStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.IffFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.UniFact.ThenFacts {
		ok, err := ver.VerFactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.newMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFact(toCheckFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}
