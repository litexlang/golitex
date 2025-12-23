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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GenerateUndeclaredRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := envMgr.IsNameDefinedOrBuiltin((randomStr), map[string]struct{}{})
		if ret.IsErr() {
			return randomStr
		}
		i++
	}
}

func (envMgr *EnvMgr) GenerateUndeclaredRandomName_AndNotInMap(m map[string]struct{}) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := envMgr.IsNameDefinedOrBuiltin(randomStr, map[string]struct{}{})
		if ret.IsErr() {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (envMgr *EnvMgr) GetFnStructFromFnTName(fnTName *ast.FnObj) (*ast.FnTemplate, glob.GlobRet) {
	if objFnTypeToFnTStruct, ok := ast.AnonymousFnToInstFnTemplate(fnTName); ok {
		return objFnTypeToFnTStruct, glob.NewEmptyGlobTrue()
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, glob.ErrRet(fmt.Errorf("fnTNameHead is not an atom"))
		}

		return envMgr.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (envMgr *EnvMgr) getFnTDef_InstFnTStructOfIt(fnTDefName ast.Atom, templateParams []ast.Obj) (*ast.FnTemplate, glob.GlobRet) {
	defOfT := envMgr.GetFnTemplateDef(fnTDefName)
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

	return fnTStruct, glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) AutoDerivedFactsMsg(originalFact string, derivedFacts []string) glob.GlobRet {
	msgs := []string{originalFact, "-- Automatically derived facts --"}
	msgs = append(msgs, derivedFacts...)
	return glob.NewGlobTrueWithMsgs(msgs)
}

func (envMgr *EnvMgr) storeSpecFactInMem(stmt *ast.SpecFactStmt) glob.GlobRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactMem.newFact(stmt)
}

func (envMgr *EnvMgr) storeSpecFactInMemAndCollect(fact *ast.SpecFactStmt, derivedFacts *[]string) glob.GlobRet {
	ret := envMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) storeTrueEqualInEqualMemNoInfer(fact *ast.SpecFactStmt) glob.GlobRet {
	mem := envMgr.CurEnv().EqualMem

	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFcs, leftGot := mem[leftAsStr]
	storedEqualRightFcs, rightGot := mem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFcs == storedEqualRightFcs {
			return glob.NewEmptyGlobTrue()
		} else {
			newEqualFcs := []ast.Obj{}
			newEqualFcs = append(newEqualFcs, *storedEqualLeftFcs...)
			newEqualFcs = append(newEqualFcs, *storedEqualRightFcs...)
			*storedEqualLeftFcs = newEqualFcs
			*storedEqualRightFcs = newEqualFcs
			return glob.NewEmptyGlobTrue()
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFcs = append(*storedEqualLeftFcs, fact.Params[1])
		mem[rightAsStr] = storedEqualLeftFcs
		return glob.NewEmptyGlobTrue()
	}

	if !leftGot && rightGot {
		*storedEqualRightFcs = append(*storedEqualRightFcs, fact.Params[0])
		mem[leftAsStr] = storedEqualRightFcs
		return glob.NewEmptyGlobTrue()
	}

	if !leftGot && !rightGot {
		newEqualFcs := []ast.Obj{fact.Params[0], fact.Params[1]}
		mem[leftAsStr] = &newEqualFcs
		mem[rightAsStr] = &newEqualFcs
		return glob.NewEmptyGlobTrue()
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) notExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, glob.GlobRet) {
	existPropDef := envMgr.GetExistPropDef(fact.PropName)
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

	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.ExistParamSets, []ast.FactStmt{}, []ast.FactStmt{orStmt}, fact.Line), glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) iffFactsInExistStFact(fact *ast.SpecFactStmt) ([]ast.FactStmt, []ast.FactStmt, glob.GlobRet) {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existPropDef := envMgr.GetExistPropDef(fact.PropName)
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

	return instantiatedIffFacts, instantiatedThenFacts, glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) StoreTrueEqualValues(key, value ast.Obj) {
	// 如果已经知道它的值了，那不能存了；否则比如我在外部环境里知道了a = 3，内部环境在反证法证明 a != 1，那我 a = 1就把a = 3覆盖掉了，a = 3这个取值貌似就不work了。某种程度上就是弄了个const
	if v := envMgr.GetSymbolSimplifiedValue(key); v != nil {
		return
	}
	envMgr.CurEnv().SymbolSimplifiedValueMem[key.String()] = value
}

func (envMgr *EnvMgr) storeSymbolSimplifiedValue(left, right ast.Obj) glob.GlobRet {
	_, newLeft := envMgr.ReplaceSymbolWithValue(left)
	if cmp.IsNumExprLitObj(newLeft) {
		simplifiedNewLeft := cmp.IsNumExprObjThenSimplify(newLeft)
		envMgr.StoreTrueEqualValues(right, simplifiedNewLeft)
	}

	_, newRight := envMgr.ReplaceSymbolWithValue(right)
	if cmp.IsNumExprLitObj(newRight) {
		simplifiedNewRight := cmp.IsNumExprObjThenSimplify(newRight)
		envMgr.StoreTrueEqualValues(left, simplifiedNewRight)
	}

	return glob.NewEmptyGlobTrue()
}

func (envMgr *EnvMgr) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMgr.CurEnv().EqualMem[objAsStr]
	return facts, ok
}

func (envMgr *EnvMgr) FnObjHeadIsAtomAndIsFnSet(fnObj *ast.FnObj) bool {
	if asAtom, ok := fnObj.FnHead.(ast.Atom); ok {
		_, ok := envMgr.AllDefinedFnSetNames[string(asAtom)]
		return ok
	}

	return false
}

func (envMgr *EnvMgr) NameWithPkgName(name string) string {
	curPkgName := envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName
	if curPkgName == "" {
		return name
	}
	return fmt.Sprintf("%s.%s", curPkgName, name)
}

func (envMgr *EnvMgr) GetEnvMgrOfPkgName(pkgName string) *EnvMgr {
	path, ok := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[pkgName]
	if !ok {
		return nil
	}

	return envMgr.EnvPkgMgr.AbsPkgPathEnvMgrMap[path]
}
