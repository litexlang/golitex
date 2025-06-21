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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com

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
	case *ast.OrStmt:
		return env.newLogicExprFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newSpecFactNoPostProcess(fact *ast.SpecFactStmt) error {
	if env.CurMatchProp == nil {
		if isEqualFact, err := env.isTrueEqualFact_StoreIt(fact); err != nil {
			return err
		} else if isEqualFact {
			return nil
		}
	}

	if isMathInductionProp, err := env.isMathInductionPropName_StoreIt(fact); err != nil {
		return err
	} else if isMathInductionProp {
		return nil
	}

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(fact, env.CurMatchEnv)
	err := env.storeSpecFactInMem(fact)
	if err != nil {
		return err
	}

	return nil
}

// 为了防止 p 的定义中推导出q，q的定义中推导出p，导致循环定义，所以需要这个函数
func (env *Env) newFactNoPostProcess(stmt ast.FactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFactNoPostProcess(f)
	case *ast.OrStmt:
		return env.newLogicExprFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newLogicExprFact(fact *ast.OrStmt) error {
	return env.storeLogicFact(fact)
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) error {
	if env.CurMatchProp == nil {
		if isEqualFact, err := env.isTrueEqualFact_StoreIt(fact); err != nil {
			return err
		} else if isEqualFact {
			return nil
		}
	}

	if isMathInductionProp, err := env.isMathInductionPropName_StoreIt(fact); err != nil {
		return err
	} else if isMathInductionProp {
		return nil
	}

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(fact, env.CurMatchEnv)
	err := env.storeSpecFactInMem(fact)
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

	existPropDef, ok := env.GetExistPropDef(fact.PropName)
	if ok {
		if fact.TypeEnum == ast.TruePure {
			return nil
		} else {
			if glob.KnowSpecFactByDef {
				for _, thenFact := range existPropDef.DefBody.IffFacts {
					_, ok := thenFact.(*ast.SpecFactStmt)
					if !ok {
						return nil
					}
				}
				return env.newFalseExistFact_EmitEquivalentUniFact(fact)
			} else {
				return nil
			}
		}
	}

	if _, ok := glob.BuiltinKeywordsSet[fact.PropName.Name]; ok || fact.IsBuiltinInfixRelaProp() {
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

		err = env.newFactNoPostProcess(instantiated)

		env.NewMsg(fmt.Sprintf("%s\nis true by definition", instantiated.String()))

		if err != nil {
			return err
		}
	}

	return nil
}

func (env *Env) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TrueExist_St {
		return env.newTrueExist_St_FactPostProcess(fact)
	} else {
		return nil
	}
}

// not exist => forall not
func (env *Env) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) error {
	uniFact, err := env.NotExistToForall(fact)
	if err != nil {
		return err
	}

	err = env.newFactNoPostProcess(uniFact)

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

	existFact := ast.NewSpecFactStmt(ast.TruePure, &fact.PropName, fact.Params[sepIndex+1:])

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, env.CurMatchEnv)
	err := env.storeSpecFactInMem(existFact)
	if err != nil {
		return err
	}

	// iff facts
	iffFacts, err := env.iffFactsInExistStFact(fact)
	if err != nil {
		return err
	}

	for _, iffFact := range iffFacts {
		err := env.NewFact(iffFact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, error) {
	existPropDef, ok := env.GetExistPropDef(fact.PropName)
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
		asSpecFactStmt, ok := thenFact.(*ast.SpecFactStmt)
		if !ok {
			return nil, fmt.Errorf("exist fact %s has no definition", fact.String())
		}

		reversedFacts := asSpecFactStmt.ReverseIsTrue()
		for _, reversedFact := range reversedFacts {
			instantiated, err := reversedFact.Instantiate(uniMap)
			if err != nil {
				return nil, err
			}
			specThenFacts = append(specThenFacts, instantiated.(*ast.SpecFactStmt))
		}
	}

	thenFacts := []ast.FactStmt{}
	for _, specThenFact := range specThenFacts {
		thenFacts = append(thenFacts, specThenFact)
	}

	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.DefBody.DefHeader.SetParams, domFacts, thenFacts), nil
}

func (env *Env) isTrueEqualFact_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithNameAndEmptyPkg(&fact.PropName, glob.KeySymbolEqual) {
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

func (env *Env) isMathInductionPropName_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if !ast.IsFcAtomWithNameAndEmptyPkg(&fact.PropName, glob.KeywordProveByMathInduction) {
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

	knownUniFactParams := []string{"n"}
	knownUniFactDomFacts := []ast.FactStmt{}
	knownUniFactThenFacts := []ast.FactStmt{
		ast.NewSpecFactStmt(
			ast.TruePure,
			propNameAsAtom,
			[]ast.Fc{ast.NewFcAtomWithName("n")},
		),
	}

	knownUniFact := ast.NewUniFact(knownUniFactParams, []ast.Fc{ast.NewFcAtomWithName(glob.KeywordNatural)}, knownUniFactDomFacts, knownUniFactThenFacts)

	err := env.NewFact(knownUniFact)
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) iffFactsInExistStFact(fact *ast.SpecFactStmt) ([]ast.FactStmt, error) {
	sepIndex := fact.Exist_St_SeparatorIndex()
	if sepIndex == -1 {
		return nil, fmt.Errorf("%s has no separator", fact.String())
	}

	existPropDef, ok := env.GetExistPropDef(fact.PropName)
	if !ok {
		return nil, fmt.Errorf("exist fact %s has no definition", fact.String())
	}

	uniMap := map[string]ast.Fc{}
	for i := range sepIndex {
		uniMap[existPropDef.ExistParams[i]] = fact.Params[i]
	}

	for i := sepIndex + 1; i < len(fact.Params); i++ {
		uniMap[existPropDef.DefBody.DefHeader.Params[i-sepIndex-1]] = fact.Params[i]
	}

	instantiatedIffFacts := []ast.FactStmt{}
	// instantiate iff facts
	for _, iffFact := range existPropDef.DefBody.IffFacts {
		instantiated, err := iffFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedIffFacts = append(instantiatedIffFacts, instantiated)
	}

	return instantiatedIffFacts, nil
}
