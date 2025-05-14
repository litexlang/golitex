// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (env *Env) NewFact(stmt ast.FactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFact(f)
	case *ast.LogicExprStmt:
		return env.newLogicExprStmt(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newLogicExprStmt(fact *ast.LogicExprStmt) error {
	return env.SpecFactInLogicExprMem.NewFact(fact)
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) error {
	if isEqualFact, err := env.IsEqualFact_StoreIt(fact); isEqualFact {
		return err
	}

	if isMathInductionProp, err := env.IsMathInductionPropName_StoreIt(fact); isMathInductionProp {
		return err
	}

	if isCommutativeProp, err := env.IsCommutativePropName_StoreIt(fact); isCommutativeProp {
		return err
	}

	if isCommutativeFn, err := env.IsCommutativeFnName_StoreIt(fact); isCommutativeFn {
		return err
	}

	if isAssociativeFn, err := env.IsAssociativeFnName_StoreIt(fact); isAssociativeFn {
		return err
	}

	if isEqualFn, err := env.IsEqualFnName_StoreIt(fact); isEqualFn {
		return err
	}

	if isEqualSet, err := env.IsEqualSetName_StoreIt(fact); isEqualSet {
		return err
	}

	err := env.SpecFactMem.NewFact(fact)
	if err != nil {
		return err
	}

	// postprocess
	if fact.IsExist_St_Fact() {
		return env.newExist_St_FactPostProcess(fact)
	}

	if fact.IsExistFact() {
		return env.newExistFactPostProcess(fact)
	}

	return env.newAtomSpecFactPostProcess(fact)
}

func storeCommutativeTransitiveFact(mem map[string]*[]ast.Fc, fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFcs, leftGot := mem[leftAsStr]
	storedEqualRightFcs, rightGot := mem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFcs == storedEqualRightFcs {
			return nil
		} else {
			newEqualFcs := []ast.Fc{}
			newEqualFcs = append(newEqualFcs, *storedEqualLeftFcs...)
			newEqualFcs = append(newEqualFcs, *storedEqualRightFcs...)
			*storedEqualLeftFcs = newEqualFcs
			*storedEqualRightFcs = newEqualFcs
			return nil
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFcs = append(*storedEqualLeftFcs, fact.Params[1])
		mem[rightAsStr] = storedEqualLeftFcs
		return nil
	}

	if !leftGot && rightGot {
		*storedEqualRightFcs = append(*storedEqualRightFcs, fact.Params[0])
		mem[leftAsStr] = storedEqualRightFcs
		return nil
	}

	if !leftGot && !rightGot {
		newEqualFcs := []ast.Fc{fact.Params[0], fact.Params[1]}
		mem[leftAsStr] = &newEqualFcs
		mem[rightAsStr] = &newEqualFcs
		return nil
	}

	return nil
}

func (env *Env) newAtomSpecFactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TruePure {
		if glob.KnowSpecFactByDef {
			return env.newFactsInSpecFactDef(fact)
		} else {
			return nil
		}
	} else {
		return nil
	}
}

func (env *Env) newFactsInSpecFactDef(fact *ast.SpecFactStmt) error {
	propDef, ok := env.GetPropDef(fact.PropName)
	if !ok {
		// TODO 这里需要考虑prop的定义是否在当前包中。当然这里有点复杂，因为如果是内置的prop，那么可能需要到builtin包中去找
		// return fmt.Errorf("prop %s has no definition", fact.PropName)
		return nil
	}

	uniMap := map[string]ast.Fc{}
	for i, propParam := range propDef.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	for _, thenFact := range propDef.IffFacts {
		instantiated, err := thenFact.Instantiate(uniMap)
		if err != nil {
			return err
		}

		err = env.NewFact(instantiated)

		env.NewMsg(fmt.Sprintf(`know by prop definition: %s`, instantiated.String()))

		if err != nil {
			return err
		}
	}

	return nil
}

func (env *Env) newExistFactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TrueExist {
		return nil
	} else {
		return env.newFalseExistFactPostProcess(fact)
	}
}

func (env *Env) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TrueExist_St {
		return env.newTrueExist_St_FactPostProcess(fact)
	} else {
		return nil
	}
}

// not exist => forall not
func (env *Env) newFalseExistFactPostProcess(fact *ast.SpecFactStmt) error {
	uniFact, err := env.NotExistToForall(fact)
	if err != nil {
		return err
	}

	err = env.storeUniFact(uniFact)
	if err != nil {
		return fmt.Errorf("exist fact %s has no definition", fact.String())
	}

	return nil
}

// have(exist ... st ...) => exist
func (env *Env) newTrueExist_St_FactPostProcess(fact *ast.SpecFactStmt) error {
	sepIndex := fact.Exist_St_SeparatorIndex()
	if sepIndex == -1 {
		return fmt.Errorf("%s has no separator", fact.String())
	}

	existFact := ast.NewSpecFactStmt(ast.TrueExist, fact.PropName, fact.Params[sepIndex+1:])

	err := env.SpecFactMem.NewFact(existFact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) newUniFact(fact *ast.UniFactStmt) error {
	// TODO: 现在只能记忆 specFact undef unifact, 理论上要让 logic_expr 也能记忆
	err := env.storeUniFact(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) IsInvalidName(name string) error {
	err := glob.IsValidName(name)
	if err != nil {
		return err
	}

	for curEnv := env; curEnv != nil; curEnv = curEnv.Parent {
		_, ok := curEnv.ObjDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordObj)
		}
		_, ok = curEnv.FnDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordFn)
		}
		_, ok = curEnv.PropDefMem.Dict[glob.EmptyPkg][name]
		if ok {
			return duplicateDefMsg(glob.EmptyPkg, name, glob.KeywordProp)
		}
	}

	return nil
}

func (env *Env) NewDefProp(stmt *ast.DefPropStmt) error {
	err := env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.PropDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefObj(stmt *ast.DefObjStmt) error {
	for _, objName := range stmt.Objs {
		err := env.IsInvalidName(objName)
		if err != nil {
			return err
		}
	}

	return env.ObjDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefFn(stmt *ast.DefFnStmt) error {
	err := env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.FnDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NewDefExistProp(stmt *ast.DefExistPropStmt) error {
	err := env.IsInvalidName(stmt.DefBody.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropDefMem.Insert(stmt, glob.EmptyPkg)
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, error) {
	if fact.TypeEnum != ast.FalseExist {
		return nil, fmt.Errorf("exist fact must have one parameter")
	}

	existPropDef, ok := env.ExistPropDefMem.Get(fact.PropName)
	if !ok {
		return nil, fmt.Errorf("exist fact %s has no definition", fact.String())
	}

	uniMap := map[string]ast.Fc{}
	for i, propParam := range existPropDef.DefBody.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, domFact := range existPropDef.DefBody.DomFacts {
		instantiated, err := domFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		domFacts = append(domFacts, instantiated)
	}

	specThenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range existPropDef.DefBody.IffFacts {
		reversed := thenFact.ReverseIsTrue()
		instantiated, err := reversed.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		specThenFacts = append(specThenFacts, instantiated.(*ast.SpecFactStmt))
	}

	thenFacts := []ast.FactStmt{}
	for _, specThenFact := range specThenFacts {
		thenFacts = append(thenFacts, specThenFact)
	}

	return ast.NewUniFactStmtWithSetReqInDom(existPropDef.ExistParams, existPropDef.ExistParamSets, domFacts, thenFacts, ast.EmptyIffFacts, existPropDef.ExistInSetsFacts), nil
}

func (env *Env) IsEqualFact_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeySymbolEqual) {
		return false, nil
	}

	if len(fact.Params) != 2 {
		return true, fmt.Errorf("`=` fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
	}

	err := storeCommutativeTransitiveFact(env.EqualMem, fact)
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) GetEqualFcs(fc ast.Fc) (*[]ast.Fc, bool) {
	fcAsStr := fc.String()
	facts, ok := env.EqualMem[fcAsStr]
	return facts, ok
}

func (env *Env) IsCommutativePropName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeywordCommutativeProp) {
		return false, nil
	}

	// 验证它的def确实只有两个元素
	if len(fact.Params) != 1 {
		return true, fmt.Errorf("commutative prop is supposed to have one parameter, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	propNameAsAtom, ok := fact.Params[0].(*ast.FcAtom)
	if !ok {
		return true, fmt.Errorf("commutative prop is supposed to have one atom parameter, but %s has %s", fact.PropName, fact.Params[0])
	}

	propDef, ok := env.PropDefMem.Get(*propNameAsAtom)
	if !ok {
		return true, fmt.Errorf("prop %s has no definition", fact.PropName)
	}

	if len(propDef.DefHeader.Params) != 2 {
		return true, fmt.Errorf("prop %s is supposed to be commutative, but has no %d parameters", fact.PropName, len(propDef.DefHeader.Params))
	}

	env.InsertCommutativeProp(*propNameAsAtom)

	return true, nil
}

func (env *Env) IsMathInductionPropName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeywordInduction) {
		return false, nil
	}

	if len(fact.Params) != 1 {
		return true, fmt.Errorf("math induction prop is supposed to have one parameter, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	propNameAsAtom, ok := fact.Params[0].(*ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name as parameter, got: %s", fact.String(), fact.Params[0])
	}

	_, ok = env.GetPropDef(*propNameAsAtom)
	if !ok {
		return false, fmt.Errorf("math induction fact %s should have a prop name that is defined, got: %s", fact.String(), propNameAsAtom)
	}

	knownUniFact := ast.UniFactStmt{
		Params:    []string{fmt.Sprintf("%sn", glob.UniParamPrefix)},
		ParamSets: []ast.Fc{ast.NewFcAtomWithName(glob.KeywordNatural)},
		DomFacts:  []ast.FactStmt{},
		ThenFacts: []ast.FactStmt{
			&ast.SpecFactStmt{
				TypeEnum: ast.TruePure,
				PropName: *propNameAsAtom,
				Params:   []ast.Fc{ast.NewFcAtomWithName(fmt.Sprintf("%sn", glob.UniParamPrefix))},
			},
		},
		IffFacts: ast.EmptyIffFacts,
	}

	err := env.NewFact(&knownUniFact)
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) IsCommutativeFnName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeywordCommutativeFn) {
		return false, nil
	}

	if len(fact.Params) != 1 {
		return false, fmt.Errorf("commutative fn is supposed to have one parameter, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	fnNameAsAtom, ok := fact.Params[0].(*ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("commutative fn is supposed to have one atom parameter, but %s has %s", fact.PropName, fact.Params[0])
	}

	env.InsertCommutativeFn(*fnNameAsAtom)

	return true, nil
}

func (env *Env) IsAssociativeFnName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeywordAssociativeFn) {
		return false, nil
	}

	if len(fact.Params) != 1 {
		return false, fmt.Errorf("associative fn is supposed to have one parameter, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	fnNameAsAtom, ok := fact.Params[0].(*ast.FcAtom)
	if !ok {
		return false, fmt.Errorf("associative fn is supposed to have one atom parameter, but %s has %s", fact.PropName, fact.Params[0])
	}

	env.InsertAssociativeFn(*fnNameAsAtom)

	return true, nil
}

func (env *Env) IsEqualFnName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeySymbolEqualEqual) {
		return false, nil
	}

	if len(fact.Params) != 2 {
		return false, fmt.Errorf("equal fn is supposed to have two parameters, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	err := storeCommutativeTransitiveFact(env.EqualMem, fact)
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) IsEqualSetName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeySymbolEqualEqualEqual) {
		return false, nil
	}

	if len(fact.Params) != 2 {
		return false, fmt.Errorf("equal set is supposed to have two parameters, but %s has %d parameters", fact.PropName, len(fact.Params))
	}

	err := storeCommutativeTransitiveFact(env.EqualMem, fact)
	if err != nil {
		return false, err
	}

	return true, nil
}
