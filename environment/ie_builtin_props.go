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

func (ie *InferEngine) equalSetFactPostProcess(fact *ast.SpecFactStmt) *glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	derivedFacts := []string{}

	// Create a = b fact
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
	if ret.IsErr() {
		return ret
	}
	derivedFacts = append(derivedFacts, equalFact.String())

	// Collect any derived facts from the equality fact
	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
	}

	if len(derivedFacts) > 0 {
		return glob.NewGlobTrueWithMsgs(derivedFacts)
	}
	return glob.NewEmptyGlobTrue()
}
