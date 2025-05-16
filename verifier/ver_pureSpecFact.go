// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import ast "golitex/ast"

func (ver *Verifier) pureSpecFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	ok, err := ver.specFactSpec(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	if state.isSpec() {
		return false, nil
	}

	ok, err = ver.specFactProveByDefinition(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		if state.requireMsg() {
			ver.successWithMsg(stmt.String(), "definition")
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}

	ok, err = ver.SpecFactUni(stmt, state)
	if err != nil {
		return false, err
	}
	if ok {
		return true, nil
	}

	return false, nil
}
