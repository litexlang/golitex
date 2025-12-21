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

func (ie *InferenceEngine) newPureFact(fact *ast.SpecFactStmt) glob.GlobRet {
	if glob.IsBuiltinPropName(string(fact.PropName)) || glob.IsBuiltinExistPropName(string(fact.PropName)) {
		ret := ie.BuiltinPropExceptTrueEqual(fact)
		return ret
	}

	propDef := ie.EnvMgr.GetPropDef(fact.PropName)

	if propDef != nil {
		if fact.TypeEnum == ast.TruePure {
			ret := ie.newUserDefinedTruePureFactByDef(fact)
			// Inherit derived facts from prop definition
			return ret
		}
		return glob.NewEmptyGlobTrue()
	}

	existPropDef := ie.EnvMgr.GetExistPropDef(fact.PropName)
	if existPropDef != nil {
		if fact.TypeEnum == ast.TruePure {
			return glob.NewEmptyGlobTrue()
		} else {
			for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
				_, ok := thenFact.(*ast.SpecFactStmt)
				if !ok {
					return glob.NewEmptyGlobTrue()
				}
			}
			ret := ie.newFalseExistFact_EmitEquivalentUniFact(fact)
			// Inherit derived facts from exist prop processing
			return ret
		}
	}

	return glob.ErrRet(fmt.Errorf("undefined prop: %s", fact.PropName))
}

// equalTupleFactPostProcess handles postprocessing for equal_tuple(a, b, dim) facts
// It automatically derives a[i] = b[i] for i from 1 to dim
func (ie *InferenceEngine) equalTupleFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 3 {
		return glob.ErrRet(fmt.Errorf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact))
	}

	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

	ret := ie.EnvMgr.NewFactWithAtomsDefined(equalFact)
	if ret.IsErr() {
		return ret
	}

	return ret
}

func (ie *InferenceEngine) newFalseExist(fact *ast.SpecFactStmt) glob.GlobRet {
	_ = fact
	return glob.NewEmptyGlobTrue()
}

// newTrueExist handles postprocessing for TrueExist_St facts
// have(exist ... st ...) => exist
func (ie *InferenceEngine) newTrueExist(fact *ast.SpecFactStmt) glob.GlobRet {
	_, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

	// err := ie.Env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, ie.Env.CurMatchEnv)

	ret := ie.EnvMgr.storeSpecFactInMem(existFact)
	if ret.IsErr() {
		return ret
	}

	// iff facts
	iffFacts, thenFacts, ret := ie.EnvMgr.iffFactsInExistStFact(fact)
	if ret.IsErr() {
		return ret
	}

	for _, iffFact := range iffFacts {
		ret := ie.EnvMgr.NewFactWithAtomsDefined(iffFact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, thenFact := range thenFacts {
		ret := ie.EnvMgr.NewFactWithAtomsDefined(thenFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}

// newFalseExistFact_EmitEquivalentUniFact handles postprocessing for FalseExist facts
// not exist => forall not
func (ie *InferenceEngine) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) glob.GlobRet {
	uniFact, ret := ie.EnvMgr.notExistToForall(fact)
	if ret.IsErr() {
		return ret
	}

	ret = ie.EnvMgr.newFactNoInfer(uniFact)

	if ret.IsErr() {
		return glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	return glob.NewEmptyGlobTrue()
}
