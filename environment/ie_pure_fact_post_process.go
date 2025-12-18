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

func (ie *InferenceEngine) newPureFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	// 如果是 transitive prop，那么需要更新 transitive prop mem
	if fact.TypeEnum == ast.TruePure && ie.Env.IsTransitiveProp(string(fact.PropName)) {
		if ie.Env.TransitivePropMem[string(fact.PropName)] == nil {
			ie.Env.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Obj)
		}
		ie.Env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(ie.Env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
	}

	if glob.IsBuiltinPropName(string(fact.PropName)) || glob.IsBuiltinExistPropName(string(fact.PropName)) {
		ret := ie.BuiltinPropExceptEqualPostProcess(fact)
		return ret
	}

	propDef := ie.Env.GetPropDef(fact.PropName)

	if propDef != nil {
		if fact.TypeEnum == ast.TruePure {
			ret := ie.Env.newTruePureFact_EmitFactsKnownByDef(fact)
			// Inherit derived facts from prop definition
			return ret
		}
		return glob.NewGlobTrue("")
	}

	existPropDef := ie.Env.GetExistPropDef(fact.PropName)
	if existPropDef != nil {
		if fact.TypeEnum == ast.TruePure {
			return glob.NewGlobTrue("")
		} else {
			for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
				_, ok := thenFact.(*ast.SpecFactStmt)
				if !ok {
					return glob.NewGlobTrue("")
				}
			}
			ret := ie.newFalseExistFact_EmitEquivalentUniFact(fact)
			// Inherit derived facts from exist prop processing
			return ret
		}
	}

	return glob.ErrRet(fmt.Errorf("undefined prop: %s", fact.PropName))
}

// equalSetFactPostProcess handles postprocessing for equal_set(a, b) facts
// It creates an equality fact a = b
func (ie *InferenceEngine) equalSetFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	derivedFacts := []string{}

	// Create a = b fact
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.Env.NewFact(equalFact)
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
	return glob.NewGlobTrue("")
}

// equalTupleFactPostProcess handles postprocessing for equal_tuple(a, b, dim) facts
// It automatically derives a[i] = b[i] for i from 1 to dim
func (ie *InferenceEngine) equalTupleFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 3 {
		return glob.ErrRet(fmt.Errorf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact))
	}

	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

	ret := ie.Env.NewFact(equalFact)
	if ret.IsErr() {
		return ret
	}

	return ret
}

func (ie *InferenceEngine) newFalseExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	return glob.NewEmptyGlobTrue()
}

// newExist_St_FactPostProcess dispatches to the appropriate Exist_St fact postprocess handler
func (ie *InferenceEngine) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	switch fact.TypeEnum {
	case ast.TrueExist_St:
		return ie.newTrueExist_St_FactPostProcess(fact)
	case ast.FalseExist_St:
		return ie.newFalseExist_St_FactPostProcess(fact)
	default:
		return glob.NewEmptyGlobErr()
	}
}

// newTrueExist_St_FactPostProcess handles postprocessing for TrueExist_St facts
// have(exist ... st ...) => exist
func (ie *InferenceEngine) newTrueExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

	// err := ie.Env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, ie.Env.CurMatchEnv)
	if fact.PropName == glob.KeywordItemExistsIn {
		ret := ie.Env.storeSpecFactInMem(existFact)
		if ret.IsErr() {
			return ret
		}
		inFact := ast.NewInFactWithObj(existParams[0], factParams[0])
		ret = ie.Env.NewFact(inFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewGlobTrue("")
	}

	ret := ie.Env.storeSpecFactInMem(existFact)
	if ret.IsErr() {
		return ret
	}

	// iff facts
	iffFacts, thenFacts, ret := ie.Env.iffFactsInExistStFact(fact)
	if ret.IsErr() {
		return ret
	}

	for _, iffFact := range iffFacts {
		ret := ie.Env.NewFact(iffFact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, thenFact := range thenFacts {
		ret := ie.Env.NewFact(thenFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

// newFalseExistFact_EmitEquivalentUniFact handles postprocessing for FalseExist facts
// not exist => forall not
func (ie *InferenceEngine) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) glob.GlobRet {
	uniFact, ret := ie.Env.NotExistToForall(fact)
	if ret.IsErr() {
		return ret
	}

	ret = ie.Env.newFactNoPostProcess(uniFact)

	if ret.IsErr() {
		return glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	return glob.NewGlobTrue("")
}

