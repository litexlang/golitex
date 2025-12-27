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

func (ie *InferEngine) newPureFact(fact *ast.SpecFactStmt) *glob.StmtRet {
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
		return glob.NewEmptyStmtTrue()
	}

	existPropDef := ie.EnvMgr.GetExistPropDef(fact.PropName)
	if existPropDef != nil {
		if fact.TypeEnum == ast.TruePure {
			return glob.NewEmptyStmtTrue()
		} else {
			for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
				_, ok := thenFact.(*ast.SpecFactStmt)
				if !ok {
					return glob.NewEmptyStmtTrue()
				}
			}
			ret := ie.newFalseExistFact_EmitEquivalentUniFact(fact)
			// Inherit derived facts from exist prop processing
			return ret
		}
	}

	return glob.ErrRet(fmt.Sprintf("undefined prop: %s", fact.PropName))
}

// equalTupleFactPostProcess handles postprocessing for equal_tuple(a, b, dim) facts
// It automatically derives a[i] = b[i] for i from 1 to dim
func (ie *InferEngine) equalTupleFactPostProcess(fact *ast.SpecFactStmt) *glob.StmtRet {
	if len(fact.Params) != 3 {
		return glob.ErrRet(fmt.Sprintf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact))
	}

	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
	if ret.IsErr() {
		return ret
	}

	return ret
}

func (ie *InferEngine) newFalseExist(fact *ast.SpecFactStmt) *glob.StmtRet {
	_ = fact
	return glob.NewEmptyStmtTrue()
}

// newTrueExist handles postprocessing for TrueExist_St facts
// have(exist ... st ...) => exist
func (ie *InferEngine) newTrueExist(fact *ast.SpecFactStmt) *glob.StmtRet {
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
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(iffFact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, thenFact := range thenFacts {
		ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(thenFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewEmptyStmtTrue()
}

// newFalseExistFact_EmitEquivalentUniFact handles postprocessing for FalseExist facts
// not exist => forall not
func (ie *InferEngine) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) *glob.StmtRet {
	uniFact, ret := ie.EnvMgr.notExistToForall(fact)
	if ret.IsErr() {
		return ret
	}

	ret = ie.EnvMgr.newFactNoInfer(uniFact)

	if ret.IsErr() {
		return glob.ErrRet(fmt.Sprintf("exist fact %s has no definition", fact))
	}

	return glob.NewEmptyStmtTrue()
}
