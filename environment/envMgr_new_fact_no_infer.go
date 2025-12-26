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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// newFactNoInfer stores facts without performing any inference.
// This is used to prevent circular definitions (e.g., p => q, q => p).
func (envMgr *EnvMgr) newFactNoInfer(stmt ast.FactStmt) *glob.GlobRet {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return envMgr.newSpecFactNoInfer(f)
	case *ast.OrStmt:
		return envMgr.newOrFactNoInfer(f)
	case *ast.UniFactStmt:
		return envMgr.newUniFactNoInfer(f)
	case *ast.UniFactWithIffStmt:
		return envMgr.newUniFactWithIffNoInfer(f)
	case *ast.EqualsFactStmt:
		return envMgr.newEqualsFactNoInfer(f)
	default:
		return glob.ErrRet(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

// newSpecFactNoInfer stores a SpecFact without performing any inference.
// It only stores the fact in memory, without triggering post-processing.
func (envMgr *EnvMgr) newSpecFactNoInfer(fact *ast.SpecFactStmt) *glob.GlobRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return envMgr.newTrueEqualNoInfer(fact)
	}

	ret := envMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// newTrueEqualNoInfer stores an equality fact without performing any inference.
// It stores the equality in the equal memory and simplifies symbol values,
// but does not trigger equality-related inferences (e.g., cart, tuple, listSet).
func (envMgr *EnvMgr) newTrueEqualNoInfer(fact *ast.SpecFactStmt) *glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	ret := envMgr.storeTrueEqualInEqualMemNoInfer(fact)
	if ret.IsErr() {
		return ret
	}

	// 如果 a = b 中，某一项是 数值型，那就算出来这个数值，卷后把它保留在equalMem中
	ret = envMgr.storeSymbolSimplifiedValue(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}

// newEqualsFactNoInfer stores an EqualsFact without performing any inference.
// It converts the EqualsFact to individual equality facts and stores them without inference.
func (envMgr *EnvMgr) newEqualsFactNoInfer(stmt *ast.EqualsFactStmt) *glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := envMgr.newSpecFactNoInfer(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) newOrFactNoInfer(fact *ast.OrStmt) *glob.GlobRet {
	ret := envMgr.CurEnv().KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
	return ret
}

func (envMgr *EnvMgr) newUniFactNoInfer(stmt *ast.UniFactStmt) *glob.GlobRet {
	for _, thenStmt := range stmt.ThenFacts {
		var ret *glob.GlobRet
		switch asFact := thenStmt.(type) {
		case *ast.SpecFactStmt:
			ret = envMgr.newUniFact_ThenFactIsSpecFact(stmt, asFact)
		case *ast.OrStmt:
			ret = envMgr.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		default:
			return glob.ErrRet(fmt.Sprintf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) newUniFactWithIffNoInfer(stmt *ast.UniFactWithIffStmt) *glob.GlobRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := envMgr.newUniFactNoInfer(thenToIff)
	if ret.IsErr() {
		return ret
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = envMgr.newUniFactNoInfer(iffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.NewEmptyGlobTrue()
}
