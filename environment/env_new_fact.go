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
	return env.KnownFacts.SpecFactInLogicExprMem.NewFact(fact)
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) error {
	if isEqualFact, err := env.isTrueEqualFact_StoreIt(fact); err != nil {
		return err
	} else if isEqualFact {
		return nil
	}

	if isMathInductionProp, err := env.isMathInductionPropName_StoreIt(fact); err != nil {
		return err
	} else if isMathInductionProp {
		return nil
	}

	if isCommutativeProp, err := env.isTrueCommutativeProp_StoreIt(fact); err != nil {
		return err
	} else if isCommutativeProp {
		return nil
	}

	if isCommutativeFn, err := env.isCommutativeFnName_StoreIt(fact); err != nil {
		return err
	} else if isCommutativeFn {
		return nil
	}

	if isAssociativeFn, err := env.isAssociativeFnName_StoreIt(fact); err != nil {
		return err
	} else if isAssociativeFn {
		return nil
	}

	if isEqualFn, err := env.isTrueFnEqual_StoreIt(fact); err != nil {
		return err
	} else if isEqualFn {
		return nil
	}

	if isEqualSet, err := env.isTrueSetEqual_StoreIt(fact); err != nil {
		return err
	} else if isEqualSet {
		return nil
	}

	err := env.KnownFacts.SpecFactMem.NewFact(fact)
	if err != nil {
		return err
	}

	// postprocess
	if fact.IsExist_St_Fact() {
		return env.newExist_St_FactPostProcess(fact)
	}

	return env.newNotExistSt_SpecFactPostProcess(fact)
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

func (env *Env) newNotExistSt_SpecFactPostProcess(fact *ast.SpecFactStmt) error {
	_, ok := env.GetPropDef(fact.PropName)

	if ok {
		if fact.TypeEnum == ast.TruePure {
			if glob.KnowSpecFactByDef {
				return env.newTrueSpecFact_EmitFactsKnownByDef(fact)
			} else {
				return nil
			}
		}
		return nil
	}

	_, ok = env.GetExistPropDef(fact.PropName)
	if ok {
		if fact.TypeEnum == ast.TruePure {
			return nil
		} else {
			if glob.KnowSpecFactByDef {
				return env.newFalseExistFact_EmitEquivelentUniFact(fact)
			} else {
				return nil
			}
		}
	}

	if fact.IsBuiltinInfixRelaProp() {
		return nil
	} else {
		return fmt.Errorf("unknown prop %s", fact.PropName)
	}

}

func (env *Env) newTrueSpecFact_EmitFactsKnownByDef(fact *ast.SpecFactStmt) error {
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

		env.NewMsg(fmt.Sprintf("%s\nis true prop definition:\n%s\n", instantiated.String(), propDef.String()))

		if err != nil {
			return err
		}
	}

	return nil
}

// func (env *Env) newExistFactPostProcess(fact *ast.SpecFactStmt) error {
// 	if fact.TypeEnum == ast.TrueExist {
// 		return nil
// 	} else {
// 		return env.newFalseExistFactPostProcess(fact)
// 	}
// }

func (env *Env) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TrueExist_St {
		return env.newTrueExist_St_FactPostProcess(fact)
	} else {
		return nil
	}
}

// not exist => forall not
func (env *Env) newFalseExistFact_EmitEquivelentUniFact(fact *ast.SpecFactStmt) error {
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

	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, fact.Params[sepIndex+1:])

	err := env.KnownFacts.SpecFactMem.NewFact(existFact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) newUniFact(fact *ast.UniFactStmt) error {
	err := env.storeUniFact(fact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, error) {
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

	return ast.NewUniFactStmtWithSetReqInDom(existPropDef.ExistParams, domFacts, thenFacts, ast.EmptyIffFacts, existPropDef.ExistInSetsFacts), nil
}

func (env *Env) isTrueEqualFact_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeySymbolEqual) {
		return false, nil
	}

	if len(fact.Params) != 2 {
		return true, fmt.Errorf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
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

func (env *Env) isTrueCommutativeProp_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeywordCommutativeProp) {
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

func (env *Env) isMathInductionPropName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeywordInduction) {
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

	knownUniFactParams := []string{fmt.Sprintf("%sn", glob.UniParamPrefix)}
	knownUniFactDomFacts := []ast.FactStmt{}
	knownUniFactThenFacts := []ast.FactStmt{
		ast.NewSpecFactStmt(
			ast.TruePure,
			*propNameAsAtom,
			[]ast.Fc{ast.NewFcAtomWithName(fmt.Sprintf("%sn", glob.UniParamPrefix))},
		),
	}
	knownUniFactParamInSetsFacts := []ast.FactStmt{}

	knownUniFact := ast.NewUniFactStmtWithSetReqInDom(knownUniFactParams, knownUniFactDomFacts, knownUniFactThenFacts, ast.EmptyIffFacts, knownUniFactParamInSetsFacts)

	err := env.NewFact(knownUniFact)
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) isCommutativeFnName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeywordCommutativeFn) {
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

func (env *Env) isAssociativeFnName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeywordAssociativeFn) {
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

func (env *Env) isTrueFnEqual_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeySymbolEqualEqual) {
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

func (env *Env) isTrueSetEqual_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		// not = 的存储和其他普通的prop一样，因为 != 没有传递性，不能像 = 一样存储
		return false, nil
	}

	if !ast.IsFcAtomWithName(&fact.PropName, glob.KeySymbolEqualEqualEqual) {
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
