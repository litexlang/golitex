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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// newFactNoInfer stores facts without performing any inference.
// This is used to prevent circular definitions (e.g., p => q, q => p).
func (env *Env) newFactNoInfer(stmt ast.FactStmt) glob.GlobRet {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFactNoInfer(f)
	case *ast.OrStmt:
		return env.newOrFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFactNoInfer(f)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

// newSpecFactNoInfer stores a SpecFact without performing any inference.
// It only stores the fact in memory, without triggering post-processing.
func (env *Env) newSpecFactNoInfer(fact *ast.SpecFactStmt) glob.GlobRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return env.newTrueEqualNoInfer(fact)
	}

	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

// newTrueEqualNoInfer stores an equality fact without performing any inference.
// It stores the equality in the equal memory and simplifies symbol values,
// but does not trigger equality-related inferences (e.g., cart, tuple, listSet).
func (env *Env) newTrueEqualNoInfer(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	ret := env.storeTrueEqualInEqualMemNoInfer(fact)
	if ret.IsErr() {
		return ret
	}

	// 如果 a = b 中，某一项是 数值型，那就算出来这个数值，卷后把它保留在equalMem中
	ret = env.storeSymbolSimplifiedValue(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

// newEqualsFactNoInfer stores an EqualsFact without performing any inference.
// It converts the EqualsFact to individual equality facts and stores them without inference.
func (env *Env) newEqualsFactNoInfer(stmt *ast.EqualsFactStmt) glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := env.newSpecFactNoInfer(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

