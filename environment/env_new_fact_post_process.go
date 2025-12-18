// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

// import (
// 	"fmt"
// 	ast "golitex/ast"
// 	glob "golitex/glob"
// )

func storeCommutativeTransitiveFact(mem map[string]*[]ast.Obj, fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFcs, leftGot := mem[leftAsStr]
	storedEqualRightFcs, rightGot := mem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFcs == storedEqualRightFcs {
			return glob.NewGlobTrue("")
		} else {
			newEqualFcs := []ast.Obj{}
			newEqualFcs = append(newEqualFcs, *storedEqualLeftFcs...)
			newEqualFcs = append(newEqualFcs, *storedEqualRightFcs...)
			*storedEqualLeftFcs = newEqualFcs
			*storedEqualRightFcs = newEqualFcs
			return glob.NewGlobTrue("")
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFcs = append(*storedEqualLeftFcs, fact.Params[1])
		mem[rightAsStr] = storedEqualLeftFcs
		return glob.NewGlobTrue("")
	}

	if !leftGot && rightGot {
		*storedEqualRightFcs = append(*storedEqualRightFcs, fact.Params[0])
		mem[leftAsStr] = storedEqualRightFcs
		return glob.NewGlobTrue("")
	}

	if !leftGot && !rightGot {
		newEqualFcs := []ast.Obj{fact.Params[0], fact.Params[1]}
		mem[leftAsStr] = &newEqualFcs
		mem[rightAsStr] = &newEqualFcs
		return glob.NewGlobTrue("")
	}

	return glob.NewGlobTrue("")
}

// func (env *Env) newPureFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// 	// 如果是 transitive prop，那么需要更新 transitive prop mem
// 	if fact.TypeEnum == ast.TruePure && env.IsTransitiveProp(string(fact.PropName)) {
// 		if env.TransitivePropMem[string(fact.PropName)] == nil {
// 			env.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Obj)
// 		}
// 		env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
// 	}

// 	if glob.IsBuiltinPropName(string(fact.PropName)) || glob.IsBuiltinExistPropName(string(fact.PropName)) {
// 		ret := env.BuiltinPropExceptEqualPostProcess(fact)
// 		return ret
// 	}

// 	propDef := env.GetPropDef(fact.PropName)

// 	if propDef != nil {
// 		if fact.TypeEnum == ast.TruePure {
// 			ret := env.newTruePureFact_EmitFactsKnownByDef(fact)
// 			// Inherit derived facts from prop definition
// 			return ret
// 		}
// 		return glob.NewGlobTrue("")
// 	}

// 	existPropDef := env.GetExistPropDef(fact.PropName)
// 	if existPropDef != nil {
// 		if fact.TypeEnum == ast.TruePure {
// 			return glob.NewGlobTrue("")
// 		} else {
// 			for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
// 				_, ok := thenFact.(*ast.SpecFactStmt)
// 				if !ok {
// 					return glob.NewGlobTrue("")
// 				}
// 			}
// 			ret := env.newFalseExistFact_EmitEquivalentUniFact(fact)
// 			// Inherit derived facts from exist prop processing
// 			return ret
// 		}
// 	}

// 	return glob.ErrRet(fmt.Errorf("undefined prop: %s", fact.PropName))
// }

// // equalSetFactPostProcess handles postprocessing for equal_set(a, b) facts
// // It creates an equality fact a = b
// func (env *Env) equalSetFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// 	if len(fact.Params) != 2 {
// 		return glob.ErrRet(fmt.Errorf("equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
// 	}

// 	derivedFacts := []string{}

// 	// Create a = b fact
// 	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
// 	ret := env.NewFact(equalFact)
// 	if ret.IsErr() {
// 		return ret
// 	}
// 	derivedFacts = append(derivedFacts, equalFact.String())

// 	// Collect any derived facts from the equality fact
// 	if ret.IsTrue() && len(ret.GetMsgs()) > 0 {
// 		derivedFacts = append(derivedFacts, ret.GetMsgs()...)
// 	}

// 	if len(derivedFacts) > 0 {
// 		return glob.NewGlobTrueWithMsgs(derivedFacts)
// 	}
// 	return glob.NewGlobTrue("")
// }

// // equalTupleFactPostProcess handles postprocessing for equal_tuple(a, b, dim) facts
// // It automatically derives a[i] = b[i] for i from 1 to dim
// func (env *Env) equalTupleFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// 	if len(fact.Params) != 3 {
// 		return glob.ErrRet(fmt.Errorf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact))
// 	}

// 	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

// 	ret := env.NewFact(equalFact)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	return ret
// }

// func (env *Env) newFalseExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// 	return glob.NewEmptyGlobTrue()
// }

// // newExist_St_FactPostProcess dispatches to the appropriate Exist_St fact postprocess handler
// // func (env *Env) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// // 	switch fact.TypeEnum {
// // 	case ast.TrueExist_St:
// // 		return env.newTrueExist_St_FactPostProcess(fact)
// // 	case ast.FalseExist_St:
// // 		return env.newFalseExist_St_FactPostProcess(fact)
// // 	default:
// // 		return glob.NewEmptyGlobErr()
// // 	}
// // }

// // newTrueExist_St_FactPostProcess handles postprocessing for TrueExist_St facts
// // have(exist ... st ...) => exist
// func (env *Env) newTrueExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
// 	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

// 	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

// 	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, env.CurMatchEnv)
// 	if fact.PropName == glob.KeywordItemExistsIn {
// 		ret := env.storeSpecFactInMem(existFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 		inFact := ast.NewInFactWithObj(existParams[0], factParams[0])
// 		ret = env.NewFact(inFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 		return glob.NewGlobTrue("")
// 	}

// 	ret := env.storeSpecFactInMem(existFact)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	// iff facts
// 	iffFacts, thenFacts, ret := env.iffFactsInExistStFact(fact)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	for _, iffFact := range iffFacts {
// 		ret := env.NewFact(iffFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 	}

// 	for _, thenFact := range thenFacts {
// 		ret := env.NewFact(thenFact)
// 		if ret.IsErr() {
// 			return ret
// 		}
// 	}

// 	return glob.NewGlobTrue("")
// }

// // newFalseExistFact_EmitEquivalentUniFact handles postprocessing for FalseExist facts
// // not exist => forall not
// func (env *Env) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) glob.GlobRet {
// 	uniFact, ret := env.NotExistToForall(fact)
// 	if ret.IsErr() {
// 		return ret
// 	}

// 	ret = env.newFactNoPostProcess(uniFact)

// 	if ret.IsErr() {
// 		return glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
// 	}

// 	return glob.NewGlobTrue("")
// }
