// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import ast "golitex/litex_ast"

func (ver *Verifier) CondFact(stmt *ast.CondFactStmt, state VerState) (bool, error) {
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg() // 万一cond里有condFact，那要保证能回到原来的环境

	for _, condFact := range stmt.CondFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, thenFact := range stmt.ThenFacts {
		nextState := state
		ok, err := ver.FactStmt(thenFact, nextState) // 貌似这里不用把state换成spec，比如用户输入condFact，然后下面的事实都正常运行，只不过需要现知道一下condFacts
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
		err = ver.env.NewFact(thenFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		ver.successMsgEnd(stmt.String(), "")
		return true, nil
	} else {
		ver.successNoMsg()
		return true, nil
	}
}
