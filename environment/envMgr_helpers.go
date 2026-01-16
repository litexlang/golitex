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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GenerateUndeclaredRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := envMgr.IsNameUnavailable((randomStr), map[string]struct{}{})
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
		ret := envMgr.IsNameUnavailable(randomStr, map[string]struct{}{})
		if ret.IsErr() {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (envMgr *EnvMgr) GetFnStructFromFnTName(fnTName *ast.FnObj) (*ast.AnonymousFn, *glob.ShortRet) {
	if objFnTypeToFnTStruct, ok := envMgr.AnonymousFnToInstFnTemplate(fnTName); ok {
		return objFnTypeToFnTStruct, glob.NewEmptyShortTrueRet()
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, glob.NewShortRetTrue(fmt.Sprintf("fnTNameHead is not an atom"))
		}

		return envMgr.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (envMgr *EnvMgr) getFnTDef_InstFnTStructOfIt(fnTDefName ast.Atom, templateParams []ast.Obj) (*ast.AnonymousFn, *glob.ShortRet) {
	defOfT := envMgr.GetFnTemplateDef(fnTDefName)
	if defOfT == nil {
		return nil, glob.NewShortRetErr(fmt.Sprintf("fnTNameHead %s is not a fn template", fnTDefName))
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, glob.NewShortRetErr(err.Error())
	}

	fnTStruct, err := defOfT.AnonymousFn.Instantiate(uniMap)
	if err != nil {
		return nil, glob.NewShortRetErr(err.Error())
	}

	return fnTStruct, glob.NewEmptyShortTrueRet()
}

func (envMgr *EnvMgr) storeSpecFactInMem(stmt *ast.SpecFactStmt) *glob.StmtRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactMem.newFact(stmt)
}

func (envMgr *EnvMgr) StoreSpecFactInImplyTemplateMem(specFact ast.Spec_OrFact, implyTemplate *ast.InferTemplateStmt) *glob.StmtRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactInImplyTemplateMem.newFact(specFact, implyTemplate)
}

func (envMgr *EnvMgr) storeTrueEqualInEqualMemNoInfer(fact *ast.SpecFactStmt) *glob.StmtRet {
	mem := envMgr.CurEnv().EqualMem

	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFcs, leftGot := mem[leftAsStr]
	storedEqualRightFcs, rightGot := mem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFcs == storedEqualRightFcs {
			return glob.NewEmptyStmtTrue()
		} else {
			newEqualFcs := []ast.Obj{}
			newEqualFcs = append(newEqualFcs, *storedEqualLeftFcs...)
			newEqualFcs = append(newEqualFcs, *storedEqualRightFcs...)
			*storedEqualLeftFcs = newEqualFcs
			*storedEqualRightFcs = newEqualFcs
			return glob.NewEmptyStmtTrue()
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFcs = append(*storedEqualLeftFcs, fact.Params[1])
		mem[rightAsStr] = storedEqualLeftFcs
		return glob.NewEmptyStmtTrue()
	}

	if !leftGot && rightGot {
		*storedEqualRightFcs = append(*storedEqualRightFcs, fact.Params[0])
		mem[leftAsStr] = storedEqualRightFcs
		return glob.NewEmptyStmtTrue()
	}

	if !leftGot && !rightGot {
		newEqualFcs := []ast.Obj{fact.Params[0], fact.Params[1]}
		mem[leftAsStr] = &newEqualFcs
		mem[rightAsStr] = &newEqualFcs
		return glob.NewEmptyStmtTrue()
	}

	return glob.NewEmptyStmtTrue()
}

// func (envMgr *EnvMgr) notExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, *glob.StmtRet) {
// 	existPropDef := envMgr.GetExistPropDef(fact.PropName)
// 	if existPropDef == nil {
// 		return nil, glob.ErrRet(fmt.Sprintf("exist fact %s has no definition", fact))
// 	}

// 	uniMap := map[string]ast.Obj{}
// 	for i, propParam := range existPropDef.DefBody.DefHeader.Params {
// 		uniMap[propParam] = fact.Params[i]
// 	}

// 	// IffFactsOrNil 中的 facts 是 OR 关系，先实例化它们
// 	orFactOrs := []*ast.SpecFactStmt{}
// 	for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
// 		asSpecFactStmt, ok := thenFact.(*ast.SpecFactStmt)
// 		if !ok {
// 			return nil, glob.ErrRet(fmt.Sprintf("exist fact %s has no definition", fact))
// 		}

// 		instantiated, err := asSpecFactStmt.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, glob.ErrRetWithErr(err)
// 		}

// 		reversedFact := instantiated.(*ast.SpecFactStmt).ReverseIsTrue()

// 		orFactOrs = append(orFactOrs, reversedFact[0])
// 	}

// 	// 创建 OrStmt 表示 OR 关系，然后整体取反
// 	orStmt := ast.NewOrStmt(orFactOrs, existPropDef.Line)

// 	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.ExistParamSets, []ast.FactStmt{}, []ast.FactStmt{orStmt}, fact.Line), glob.NewEmptyStmtTrue()
// }

// func (envMgr *EnvMgr) iffFactsInExistStFact(fact *ast.SpecFactStmt) ([]ast.FactStmt, []ast.FactStmt, *glob.StmtRet) {
// 	existParams, factParams := fact.ExistStFactToPropNameExistParamsParams()

// 	existPropDef := envMgr.GetExistPropDef(fact.PropName)
// 	if existPropDef == nil {
// 		return nil, nil, glob.ErrRet(fmt.Sprintf("exist fact %s has no definition", fact))
// 	}

// 	uniMap := map[string]ast.Obj{}
// 	for i := range existParams {
// 		uniMap[existPropDef.ExistParams[i]] = existParams[i]
// 	}

// 	for i := range factParams {
// 		uniMap[existPropDef.DefBody.DefHeader.Params[i]] = factParams[i]
// 	}

// 	instantiatedIffFacts := []ast.FactStmt{}
// 	// instantiate iff facts
// 	for _, iffFact := range existPropDef.DefBody.IffFactsOrNil {
// 		instantiated, err := iffFact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, nil, glob.ErrRetWithErr(err)
// 		}
// 		instantiatedIffFacts = append(instantiatedIffFacts, instantiated)
// 	}

// 	instantiatedThenFacts := []ast.FactStmt{}
// 	for _, thenFact := range existPropDef.DefBody.ImplicationFactsOrNil {
// 		instantiated, err := thenFact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, nil, glob.ErrRetWithErr(err)
// 		}
// 		instantiatedThenFacts = append(instantiatedThenFacts, instantiated)
// 	}

// 	return instantiatedIffFacts, instantiatedThenFacts, glob.NewEmptyStmtTrue()
// }

func (envMgr *EnvMgr) StoreTrueEqualValues(key, value ast.Obj) {
	// 如果已经知道它的值了，那不能存了；否则比如我在外部环境里知道了a = 3，内部环境在反证法证明 a != 1，那我 a = 1就把a = 3覆盖掉了，a = 3这个取值貌似就不work了。某种程度上就是弄了个const
	if v := envMgr.GetSymbolSimplifiedValue(key); v != nil {
		return
	}
	envMgr.CurEnv().SymbolSimplifiedValueMem[key.String()] = value
}

func (envMgr *EnvMgr) storeSymbolSimplifiedValue(left, right ast.Obj) *glob.StmtRet {
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

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMgr.CurEnv().EqualMem[objAsStr]
	if ok {
		return facts, ok
	}

	// Search in builtin env
	facts, ok = BuiltinEnvMgrWithEmptyEnvPkgMgr.EnvSlice[0].EqualMem[objAsStr]
	return facts, ok
}

func (envMgr *EnvMgr) FnObjHeadIsAtomAndIsFnSet(fnObj *ast.FnObj) bool {
	if asAtom, ok := fnObj.FnHead.(ast.Atom); ok {
		_, ok := envMgr.AllDefinedFnSetNames[string(asAtom)]
		return ok
	}

	return false
}

func (envMgr *EnvMgr) GetEnvMgrOfPkgName(pkgName string) *EnvMgr {
	path, ok := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[pkgName]
	if !ok {
		return nil
	}

	return envMgr.EnvPkgMgr.AbsPkgPathEnvMgrMap[path]
}

var BuiltinEnvMgrWithEmptyEnvPkgMgr *EnvMgr = nil

// func CopyEnvMgrAndOwnPkgMgr(givenEnvMgr *EnvMgr, envPkgMgr *EnvPkgMgr) *EnvMgr {
// 	// 复制所有的 map
// 	allDefinedAtomObjNames := make(map[string]struct{})
// 	for k, v := range givenEnvMgr.AllDefinedAtomObjNames {
// 		allDefinedAtomObjNames[k] = v
// 	}

// 	allDefinedPropNames := make(map[string]*ast.DefPropStmt)
// 	for k, v := range givenEnvMgr.AllDefinedPropNames {
// 		allDefinedPropNames[k] = v
// 	}

// 	allDefinedExistPropNames := make(map[string]*ast.DefExistPropStmt)
// 	for k, v := range givenEnvMgr.AllDefinedExistPropNames {
// 		allDefinedExistPropNames[k] = v
// 	}

// 	allDefinedFnSetNames := make(map[string]*ast.DefFnSetStmt)
// 	for k, v := range givenEnvMgr.AllDefinedFnSetNames {
// 		allDefinedFnSetNames[k] = v
// 	}

// 	allDefinedAlgoNames := make(map[string]*ast.DefAlgoStmt)
// 	for k, v := range givenEnvMgr.AllDefinedAlgoNames {
// 		allDefinedAlgoNames[k] = v
// 	}

// 	allDefinedProveAlgoNames := make(map[string]*ast.DefProveAlgoStmt)
// 	for k, v := range givenEnvMgr.AllDefinedProveAlgoNames {
// 		allDefinedProveAlgoNames[k] = v
// 	}

// 	// 复制 EnvSlice
// 	envSlice := make([]EnvMemory, len(givenEnvMgr.EnvSlice))
// 	for i, envMem := range givenEnvMgr.EnvSlice {
// 		envSlice[i] = copyEnvMemory(envMem)
// 	}

// 	return NewEnvMgr(
// 		envPkgMgr,
// 		envSlice,
// 		allDefinedAtomObjNames,
// 		allDefinedPropNames,
// 		allDefinedExistPropNames,
// 		allDefinedFnSetNames,
// 		allDefinedAlgoNames,
// 		allDefinedProveAlgoNames,
// 	)
// }

// copyEnvMemory 深拷贝 EnvMemory
// func copyEnvMemory(src EnvMemory) EnvMemory {
// 	dst := EnvMemory{
// 		AtomObjDefMem:            make(map[string]struct{}),
// 		PropDefMem:               make(map[string]struct{}),
// 		FnTemplateDefMem:         make(map[string]struct{}),
// 		ExistPropDefMem:          make(map[string]struct{}),
// 		AlgoDefMem:               make(map[string]struct{}),
// 		DefProveAlgoMem:          make(map[string]struct{}),
// 		EqualMem:                 make(map[string]shared_ptr_to_slice_of_obj),
// 		SymbolSimplifiedValueMem: make(map[string]ast.Obj),
// 		TransitivePropMem:        make(map[string]map[string][]ast.Obj),
// 		CommutativePropMem:       make(map[string]*PropCommutativeCase),
// 		FnInFnTemplateFactsMem:   make(FnInFnTMem),
// 	}

// 	// 复制定义内存
// 	for k := range src.AtomObjDefMem {
// 		dst.AtomObjDefMem[k] = struct{}{}
// 	}
// 	for k := range src.PropDefMem {
// 		dst.PropDefMem[k] = struct{}{}
// 	}
// 	for k := range src.FnTemplateDefMem {
// 		dst.FnTemplateDefMem[k] = struct{}{}
// 	}
// 	for k := range src.ExistPropDefMem {
// 		dst.ExistPropDefMem[k] = struct{}{}
// 	}
// 	for k := range src.AlgoDefMem {
// 		dst.AlgoDefMem[k] = struct{}{}
// 	}
// 	for k := range src.DefProveAlgoMem {
// 		dst.DefProveAlgoMem[k] = struct{}{}
// 	}

// 	// 复制 EqualMem
// 	for k, v := range src.EqualMem {
// 		if v != nil {
// 			newSlice := make([]ast.Obj, len(*v))
// 			copy(newSlice, *v)
// 			dst.EqualMem[k] = &newSlice
// 		}
// 	}

// 	// 复制 SymbolSimplifiedValueMem
// 	for k, v := range src.SymbolSimplifiedValueMem {
// 		dst.SymbolSimplifiedValueMem[k] = v
// 	}

// 	// 复制 TransitivePropMem
// 	for k, v := range src.TransitivePropMem {
// 		newMap := make(map[string][]ast.Obj)
// 		for k2, v2 := range v {
// 			newSlice := make([]ast.Obj, len(v2))
// 			copy(newSlice, v2)
// 			newMap[k2] = newSlice
// 		}
// 		dst.TransitivePropMem[k] = newMap
// 	}

// 	// 复制 CommutativePropMem
// 	for k, v := range src.CommutativePropMem {
// 		if v != nil {
// 			dst.CommutativePropMem[k] = &PropCommutativeCase{
// 				TruePureIsCommutative:  v.TruePureIsCommutative,
// 				FalsePureIsCommutative: v.FalsePureIsCommutative,
// 			}
// 		}
// 	}

// 	// 复制 FnInFnTemplateFactsMem
// 	for k, v := range src.FnInFnTemplateFactsMem {
// 		newSlice := make([]FnInFnTMemItem, len(v))
// 		copy(newSlice, v)
// 		dst.FnInFnTemplateFactsMem[k] = newSlice
// 	}

// 	// 复制 KnownFactsStruct
// 	dst.KnownFactsStruct = copyKnownFactsStruct(src.KnownFactsStruct)

// 	return dst
// }

// copyKnownFactsStruct 深拷贝 KnownFactsStruct
// func copyKnownFactsStruct(src KnownFactsStruct) KnownFactsStruct {
// 	return KnownFactsStruct{
// 		SpecFactMem:                       copySpecFactMem(src.SpecFactMem),
// 		SpecFactInLogicExprMem:            copySpecFactInLogicExprMem(src.SpecFactInLogicExprMem),
// 		SpecFactInUniFactMem:              copySpecFactInUniFactMem(src.SpecFactInUniFactMem),
// 		SpecFact_InLogicExpr_InUniFactMem: copySpecFact_InLogicExpr_InUniFactMem(src.SpecFact_InLogicExpr_InUniFactMem),
// 	}
// }

// copySpecFactMem 深拷贝 SpecFactMem
// func copySpecFactMem(src SpecFactMem) SpecFactMem {
// 	dst := SpecFactMem{
// 		PureFacts:         make(map[string][]ast.SpecFactStmt),
// 		NotPureFacts:      make(map[string][]ast.SpecFactStmt),
// 		Exist_St_Facts:    make(map[string][]ast.SpecFactStmt),
// 		NotExist_St_Facts: make(map[string][]ast.SpecFactStmt),
// 	}
// 	for k, v := range src.PureFacts {
// 		dst.PureFacts[k] = append([]ast.SpecFactStmt{}, v...)
// 	}
// 	for k, v := range src.NotPureFacts {
// 		dst.NotPureFacts[k] = append([]ast.SpecFactStmt{}, v...)
// 	}
// 	for k, v := range src.Exist_St_Facts {
// 		dst.Exist_St_Facts[k] = append([]ast.SpecFactStmt{}, v...)
// 	}
// 	for k, v := range src.NotExist_St_Facts {
// 		dst.NotExist_St_Facts[k] = append([]ast.SpecFactStmt{}, v...)
// 	}
// 	return dst
// }

// // copySpecFactInLogicExprMem 深拷贝 SpecFactInLogicExprMem
// func copySpecFactInLogicExprMem(src SpecFactInLogicExprMem) SpecFactInLogicExprMem {
// 	dst := SpecFactInLogicExprMem{
// 		PureFacts:         make(map[string][]KnownSpecFact_InLogicExpr),
// 		NotPureFacts:      make(map[string][]KnownSpecFact_InLogicExpr),
// 		Exist_St_Facts:    make(map[string][]KnownSpecFact_InLogicExpr),
// 		NotExist_St_Facts: make(map[string][]KnownSpecFact_InLogicExpr),
// 	}
// 	for k, v := range src.PureFacts {
// 		dst.PureFacts[k] = append([]KnownSpecFact_InLogicExpr{}, v...)
// 	}
// 	for k, v := range src.NotPureFacts {
// 		dst.NotPureFacts[k] = append([]KnownSpecFact_InLogicExpr{}, v...)
// 	}
// 	for k, v := range src.Exist_St_Facts {
// 		dst.Exist_St_Facts[k] = append([]KnownSpecFact_InLogicExpr{}, v...)
// 	}
// 	for k, v := range src.NotExist_St_Facts {
// 		dst.NotExist_St_Facts[k] = append([]KnownSpecFact_InLogicExpr{}, v...)
// 	}
// 	return dst
// }

// // copySpecFactInUniFactMem 深拷贝 SpecFactInUniFactMem
// func copySpecFactInUniFactMem(src SpecFactInUniFactMem) SpecFactInUniFactMem {
// 	dst := SpecFactInUniFactMem{
// 		PureFacts:         make(map[string][]KnownSpecFact_InUniFact),
// 		NotPureFacts:      make(map[string][]KnownSpecFact_InUniFact),
// 		Exist_St_Facts:    make(map[string][]KnownSpecFact_InUniFact),
// 		NotExist_St_Facts: make(map[string][]KnownSpecFact_InUniFact),
// 	}
// 	for k, v := range src.PureFacts {
// 		dst.PureFacts[k] = append([]KnownSpecFact_InUniFact{}, v...)
// 	}
// 	for k, v := range src.NotPureFacts {
// 		dst.NotPureFacts[k] = append([]KnownSpecFact_InUniFact{}, v...)
// 	}
// 	for k, v := range src.Exist_St_Facts {
// 		dst.Exist_St_Facts[k] = append([]KnownSpecFact_InUniFact{}, v...)
// 	}
// 	for k, v := range src.NotExist_St_Facts {
// 		dst.NotExist_St_Facts[k] = append([]KnownSpecFact_InUniFact{}, v...)
// 	}
// 	return dst
// }

// // copySpecFact_InLogicExpr_InUniFactMem 深拷贝 SpecFact_InLogicExpr_InUniFactMem
// func copySpecFact_InLogicExpr_InUniFactMem(src SpecFact_InLogicExpr_InUniFactMem) SpecFact_InLogicExpr_InUniFactMem {
// 	dst := SpecFact_InLogicExpr_InUniFactMem{
// 		PureFacts:         make(map[string][]SpecFact_InLogicExpr_InUniFact),
// 		NotPureFacts:      make(map[string][]SpecFact_InLogicExpr_InUniFact),
// 		Exist_St_Facts:    make(map[string][]SpecFact_InLogicExpr_InUniFact),
// 		NotExist_St_Facts: make(map[string][]SpecFact_InLogicExpr_InUniFact),
// 	}
// 	for k, v := range src.PureFacts {
// 		dst.PureFacts[k] = append([]SpecFact_InLogicExpr_InUniFact{}, v...)
// 	}
// 	for k, v := range src.NotPureFacts {
// 		dst.NotPureFacts[k] = append([]SpecFact_InLogicExpr_InUniFact{}, v...)
// 	}
// 	for k, v := range src.Exist_St_Facts {
// 		dst.Exist_St_Facts[k] = append([]SpecFact_InLogicExpr_InUniFact{}, v...)
// 	}
// 	for k, v := range src.NotExist_St_Facts {
// 		dst.NotExist_St_Facts[k] = append([]SpecFact_InLogicExpr_InUniFact{}, v...)
// 	}
// 	return dst
// }

func (envMgr *EnvMgr) MakeExistFactStructDoesNotConflictWithDefinedNames(existFactStruct *ast.ExistStFactStruct, definedParams []string) (*ast.ExistStFactStruct, error) {
	uniMap := map[string]struct{}{}
	for _, param := range definedParams {
		uniMap[param] = struct{}{}
	}

	defined := false
	for _, existParam := range existFactStruct.ExistFreeParams {
		if envMgr.lookupAtomObjName(ast.Atom(existParam), uniMap).IsTrue() {
			defined = true
			break
		}
	}

	if !defined {
		return existFactStruct, nil
	}

	// 生产一个不冲突的exist fact struct
	newExistParams := make([]string, len(existFactStruct.ExistFreeParams))
	for i := range existFactStruct.ExistFreeParams {
		newExistParams[i] = envMgr.GenerateUndeclaredRandomName_AndNotInMap(uniMap)
	}

	// 把 set 也换成不冲突的
	uniMap2 := map[string]ast.Obj{}
	newExistParamSets := make([]ast.Obj, len(existFactStruct.ExistFreeParamSets))
	for i, paramSet := range existFactStruct.ExistFreeParamSets {
		newParamSet, err := paramSet.Instantiate(uniMap2)
		if err != nil {
			return nil, err
		}
		newExistParamSets[i] = newParamSet
		uniMap2[existFactStruct.ExistFreeParams[i]] = ast.Atom(newExistParams[i])
	}

	newParams := make([]ast.Obj, len(existFactStruct.Params))
	for i, param := range existFactStruct.Params {
		newParam, err := param.Instantiate(uniMap2)
		if err != nil {
			return nil, err
		}
		newParams[i] = newParam
	}

	return ast.NewExistStFactStruct(existFactStruct.FactType, existFactStruct.PropName, existFactStruct.IsPropTrue, newExistParams, newExistParamSets, newParams, existFactStruct.Line), nil
}

// storeSpecFactInMemAndCollect collects the fact string for derived facts tracking
func (ie *InferEngine) storeSpecFactInMemAndCollect(fact *ast.SpecFactStmt, derivedFacts *[]string) *glob.ShortRet {
	ret := ie.EnvMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return glob.NewEmptyShortTrueRet()
}

func (envMgr *EnvMgr) AnonymousFnToInstFnTemplate(objFnTypeT *ast.FnObj) (*ast.AnonymousFn, bool) {
	ok, paramSets, retSet := objFnTypeT.GetParamSetsAndRetSetOfAnonymousFn(objFnTypeT)
	if !ok {
		return nil, false
	}

	randomParams := []string{}
	for range len(paramSets) {
		randomParams = append(randomParams, envMgr.GenerateUndeclaredRandomName())
	}

	return ast.NewFnTStruct(randomParams, paramSets, retSet, []ast.FactStmt{}, []ast.FactStmt{}, glob.BuiltinLine0), true
}
