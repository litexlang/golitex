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

func (ie *InferEngine) newPureFact(fact *ast.SpecFactStmt) *glob.ShortRet {
	if glob.IsBuiltinPropName(string(fact.PropName)) || glob.IsBuiltinExistPropName(string(fact.PropName)) {
		ret := ie.BuiltinPropExceptTrueEqual(fact)
		return ret
	}

	propDef := ie.EnvMgr.GetPropDef(fact.PropName)

	if propDef != nil {
		if fact.FactType == ast.TruePure {
			ret := ie.newUserDefinedTruePureFactByDef(fact)
			return ret
		}
		return glob.NewEmptyShortTrueRet()
	}

	// existPropDef := ie.EnvMgr.GetExistPropDef(fact.PropName)
	// if existPropDef != nil {
	// 	if fact.FactType == ast.TruePure {
	// 		return glob.NewEmptyShortTrueRet()
	// 	} else {
	// 		for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
	// 			_, ok := thenFact.(*ast.SpecFactStmt)
	// 			if !ok {
	// 				return glob.NewEmptyShortTrueRet()
	// 			}
	// 		}
	// 		ret := ie.newFalseExistFact_EmitEquivalentUniFact(fact)
	// 		// Inherit derived facts from exist prop processing
	// 		return ret
	// 	}
	// }

	return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("undefined prop: %s", fact.PropName)})
}

// equalTupleFactPostProcess handles postprocessing for equal_tuple(a, b, dim) facts
// It automatically derives a[i] = b[i] for i from 1 to dim
func (ie *InferEngine) equalTupleFactPostProcess(fact *ast.SpecFactStmt) *glob.ShortRet {
	if len(fact.Params) != 3 {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact)})
	}

	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(equalFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, ret.Infer)
}

func (ie *InferEngine) newFalseExist(fact *ast.SpecFactStmt) *glob.ShortRet {
	existStruct := fact.ToExistStFactStruct()
	equivalentForall := ast.NewUniFact(existStruct.ExistFreeParams, existStruct.ExistFreeParamSets, []ast.FactStmt{}, []ast.FactStmt{existStruct.GetTruePureFact().ReverseTrue()}, fact.Line)
	ret := ie.EnvMgr.newUniFact(equivalentForall)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}

	return glob.NewShortRet(glob.StmtRetTypeTrue, []string{equivalentForall.String()})
}

// newTrueExist handles postprocessing for TrueExist_St facts
// have(exist ... st ...) => exist
// func (ie *InferEngine) newTrueExist(fact *ast.SpecFactStmt) *glob.ShortRet {
// 	if ie.EnvMgr.GetPropDef(fact.PropName) != nil {
// 		return glob.NewEmptyShortTrueRet()
// 	}

// 	return glob.NewShortRetErr(fmt.Sprintf("undefined prop: %s", fact.PropName))

// _, factParams := fact.ExistStFactToPropNameExistParamsParams()

// existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

// // err := ie.Env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, ie.Env.CurMatchEnv)

// ret := ie.EnvMgr.storeSpecFactInMem(existFact)
// if ret.IsErr() {
// 	return glob.ErrStmtMsgToShortRet(ret)
// }

// // iff facts
// iffFacts, thenFacts, ret := ie.EnvMgr.iffFactsInExistStFact(fact)
// if ret.IsErr() {
// 	return glob.ErrStmtMsgToShortRet(ret)
// }

// for _, iffFact := range iffFacts {
// 	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(iffFact)
// 	if ret.IsErr() {
// 		return glob.ErrStmtMsgToShortRet(ret)
// 	}
// }

// for _, thenFact := range thenFacts {
// 	ret := ie.EnvMgr.NewFactWithoutCheckingNameDefined(thenFact)
// 	if ret.IsErr() {
// 		return glob.ErrStmtMsgToShortRet(ret)
// 	}
// }

// return glob.NewEmptyShortTrueRet()
// }

// newFalseExistFact_EmitEquivalentUniFact handles postprocessing for FalseExist facts
// not exist => forall not
// func (ie *InferEngine) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) *glob.ShortRet {
// 	uniFact, ret := ie.EnvMgr.notExistToForall(fact)
// 	if ret.IsErr() {
// 		return glob.ErrStmtMsgToShortRet(ret)
// 	}

// 	ret = ie.EnvMgr.newFactNoInfer(uniFact)

// 	if ret.IsErr() {
// 		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("exist fact %s has no definition", fact)})
// 	}

// 	return glob.NewEmptyShortTrueRet()
// }
