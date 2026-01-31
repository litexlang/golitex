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
	ast "golitex/ast"
	"maps"
)

// usedNames 一般用来传递forall里的自由变量
func (envMgr *EnvMgr) GenerateNoDuplicateNames(length int, usedNames map[string]struct{}) []string {
	copiedUsedNames := maps.Clone(usedNames)
	names := make([]string, length)
	for i := 0; i < length; i++ {
		names[i] = envMgr.GenerateUnusedRandomNameWhichIsAlsoNotInGivenMap(copiedUsedNames)
		copiedUsedNames[names[i]] = struct{}{}
	}
	return names
}

func (e *EnvMgr) MatchExistSpecificFacts(given *ast.ExistSpecificFactStmt, stored *ast.ExistSpecificFactStmt, newExistFreeParams []string) bool {
	if len(stored.ExistFreeParams) != len(given.ExistFreeParams) {
		return false
	}

	if given.IsTrue != stored.IsTrue {
		return false
	}

	if given.PureFact.IsTrue != stored.PureFact.IsTrue {
		return false
	}

	newExistSpecificFactStmt, err := given.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return false
	}

	newStoredExistSpecificFactStmt, err := stored.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return false
	}

	if newExistSpecificFactStmt.String() == newStoredExistSpecificFactStmt.String() {
		return true
	}

	return false
}
