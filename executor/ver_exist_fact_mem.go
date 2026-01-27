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

// func (ver *Verifier) iterateKnownExistFactsAndMatchGivenFact(stmt ast.SpecificFactStmt, knownFacts []ast.SpecificFactStmt, state *VerState) *glob.VerRet {
// LoopOverFacts:
// 	for _, knownFact := range knownFacts {
// 		verRet := ver.MatchExistFact(stmt.(*ast.ExistSpecificFactStmt), knownFact.(*ast.ExistSpecificFactStmt), state)
// 		if verRet.IsErr() {
// 			return verRet
// 		}
// 		if verRet.IsUnknown() {
// 			continue LoopOverFacts
// 		}

// 		if state.WithMsg {
// 			return successVerString(stmt, knownFact)
// 		}
// 		return glob.NewEmptyVerRetTrue()
// 	}

// 	return glob.NewEmptyVerRetUnknown()
// }
