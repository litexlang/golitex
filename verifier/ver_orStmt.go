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
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) verOrStmt(stmt *ast.OrStmt, state VerState) (bool, error) {
	nextState := state.addRound()
	for i := range stmt.Facts {
		ok, err := ver.verFactAtIndex_WhenOthersAreFalse(stmt.Facts, i, nextState)
		if err != nil {
			return false, err
		}
		if ok {
			return true, nil
		}
	}
	return false, nil
}

func (ver *Verifier) verFactAtIndex_WhenOthersAreFalse(facts []ast.SpecFactStmt, i int, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchProp)
	defer ver.deleteEnvAndRetainMsg()

	for j := range facts {
		if j == i {
			continue
		}
		err := ver.env.NewFact(facts[j].ReverseTrue())
		if err != nil {
			return false, err
		}
	}

	ok, err := ver.FactStmt(&facts[i], state)
	if err != nil {
		return false, err
	}
	return ok, nil
}
