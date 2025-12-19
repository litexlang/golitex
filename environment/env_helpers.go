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

func (e *Env) GenerateUndeclaredRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := e.IsNameDefinedOrBuiltin((randomStr), map[string]struct{}{})
		if ret.IsErr() {
			return randomStr
		}
		i++
	}
}

func (e *Env) GenerateUndeclaredRandomName_AndNotInMap(m map[string]struct{}) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := e.IsNameDefinedOrBuiltin(randomStr, map[string]struct{}{})
		if ret.IsErr() {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (e *Env) GetFnStructFromFnTName(fnTName *ast.FnObj) (*ast.FnTStruct, glob.GlobRet) {
	if objFnTypeToFnTStruct, ok := ast.ObjFnT_To_FnTStruct(fnTName); ok {
		return objFnTypeToFnTStruct, glob.NewGlobTrue("")
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, glob.ErrRet(fmt.Errorf("fnTNameHead is not an atom"))
		}

		return e.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (e *Env) getFnTDef_InstFnTStructOfIt(fnTDefName ast.Atom, templateParams []ast.Obj) (*ast.FnTStruct, glob.GlobRet) {
	defOfT := e.GetFnTemplateDef(fnTDefName)
	if defOfT == nil {
		return nil, glob.ErrRet(fmt.Errorf("fnTNameHead %s is not a fn template", fnTDefName))
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, glob.ErrRet(err)
	}

	fnTStruct, err := defOfT.Fn.Instantiate(uniMap)
	if err != nil {
		return nil, glob.ErrRet(err)
	}

	return fnTStruct, glob.NewGlobTrue("")
}

func (e *Env) AutoDerivedFactsMsg(originalFact string, derivedFacts []string) glob.GlobRet {
	msgs := []string{originalFact, "-- Automatically derived facts --"}
	msgs = append(msgs, derivedFacts...)
	return glob.NewGlobTrueWithMsgs(msgs)
}

func (env *Env) storeSpecFactInMemAndCollect(fact *ast.SpecFactStmt, derivedFacts *[]string) glob.GlobRet {
	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return glob.NewGlobTrue("")
}

func (env *Env) storeTrueEqualInEqualMemNoInfer(fact *ast.SpecFactStmt) glob.GlobRet {
	mem := env.EqualMem

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

func (env *Env) notExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, glob.GlobRet) {
	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef == nil {
		return nil, glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	uniMap := map[string]ast.Obj{}
	for i, propParam := range existPropDef.DefBody.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	// IffFactsOrNil 中的 facts 是 OR 关系，先实例化它们
	orFactOrs := []*ast.SpecFactStmt{}
	for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
		asSpecFactStmt, ok := thenFact.(*ast.SpecFactStmt)
		if !ok {
			return nil, glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
		}

		instantiated, err := asSpecFactStmt.InstantiateFact(uniMap)
		if err != nil {
			return nil, glob.ErrRet(err)
		}

		reversedFact := instantiated.(*ast.SpecFactStmt).ReverseIsTrue()

		orFactOrs = append(orFactOrs, reversedFact[0])
	}

	// 创建 OrStmt 表示 OR 关系，然后整体取反
	orStmt := ast.NewOrStmt(orFactOrs, existPropDef.Line)

	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.ExistParamSets, []ast.FactStmt{}, []ast.FactStmt{orStmt}, fact.Line), glob.NewGlobTrue("")
}

func (env *Env) iffFactsInExistStFact(fact *ast.SpecFactStmt) ([]ast.FactStmt, []ast.FactStmt, glob.GlobRet) {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef == nil {
		return nil, nil, glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	uniMap := map[string]ast.Obj{}
	for i := range existParams {
		uniMap[existPropDef.ExistParams[i]] = existParams[i]
	}

	for i := range factParams {
		uniMap[existPropDef.DefBody.DefHeader.Params[i]] = factParams[i]
	}

	instantiatedIffFacts := []ast.FactStmt{}
	// instantiate iff facts
	for _, iffFact := range existPropDef.DefBody.IffFactsOrNil {
		instantiated, err := iffFact.InstantiateFact(uniMap)
		if err != nil {
			return nil, nil, glob.ErrRet(err)
		}
		instantiatedIffFacts = append(instantiatedIffFacts, instantiated)
	}

	instantiatedThenFacts := []ast.FactStmt{}
	for _, thenFact := range existPropDef.DefBody.ImplicationFactsOrNil {
		instantiated, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return nil, nil, glob.ErrRet(err)
		}
		instantiatedThenFacts = append(instantiatedThenFacts, instantiated)
	}

	return instantiatedIffFacts, instantiatedThenFacts, glob.NewGlobTrue("")
}
