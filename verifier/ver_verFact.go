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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) VerFactStmt(stmt ast.FactStmt, state VerState) (bool, error) {
	if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
		if asSpecFact.NameIs(glob.KeySymbolEqual) && asSpecFact.TypeEnum == ast.TruePure {
			return ver.verTrueEqualFact(asSpecFact, state)
		}

		return ver.verSpecFactThatIsNotTrueEqualFact(asSpecFact, state)
	}

	if asOrStmt, ok := stmt.(*ast.OrStmt); ok {
		return ver.verOrStmt(asOrStmt, state)
	}

	if asUniFact, ok := stmt.(*ast.UniFactStmt); ok {
		return ver.verUniFact(asUniFact, state)
	}

	if asEnumStmt, ok := stmt.(*ast.EnumStmt); ok {
		return ver.verEnumStmt(asEnumStmt, state)
	}

	if asUniFactWithIff, ok := stmt.(*ast.UniFactWithIffStmt); ok {
		return ver.verUniFactWithIff(asUniFactWithIff, state)
	}

	if asSetEqualStmt, ok := stmt.(*ast.SetEqualStmt); ok {
		return ver.verSetEqualStmt(asSetEqualStmt, state)
	}

	return false, fmt.Errorf("unexpected fact statement: %v", stmt)
}
