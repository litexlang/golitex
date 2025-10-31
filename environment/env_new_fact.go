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
	"strconv"
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
	case *ast.EnumStmt:
		return env.newEnumFact(f)
	case *ast.IntensionalSetStmt:
		return env.newIntensionalSetFact(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newSpecFactNoPostProcess(fact *ast.SpecFactStmt) error {
	// if env.CurMatchProp == nil {
	if isEqualFact, err := env.isTrueEqualFact_StoreIt(fact); err != nil {
		return err
	} else if isEqualFact {
		return nil
	}
	// }

	// if isMathInductionProp, err := env.isMathInductionPropName_StoreIt(fact); err != nil {
	// 	return err
	// } else if isMathInductionProp {
	// 	return nil
	// }

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(fact, env.CurMatchEnv)
	err := env.storeSpecFactInMem(fact)
	if err != nil {
		return err
	}

	return nil
}

// 为了防止 p 的定义中推导出q，q的定义中推导出p，导致循环定义，所以需要这个函数
// ? 总觉得这里的 除了 spec fact 以外，其他fact 的定义中推导出p，p的定义中推导出其他fact，也可能导致循环
func (env *Env) newFactNoPostProcess(stmt ast.FactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFactNoPostProcess(f)
	case *ast.OrStmt:
		return env.newLogicExprFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.IntensionalSetStmt:
		return env.newIntensionalSetFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	case *ast.EnumStmt:
		return env.newEnumFact(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFactNoPostProcess(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newLogicExprFact(fact *ast.OrStmt) error {
	return env.storeLogicFact(fact)
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) error {
	if isEqualFact, err := env.isTrueEqualFact_StoreIt(fact); err != nil {
		return err
	} else if isEqualFact {
		return nil
	}

	err := env.storeSpecFactInMem(fact)
	if err != nil {
		return err
	}

	// postprocess
	if fact.IsExist_St_Fact() {
		if fact.PropName == glob.KeywordItemExistsIn {
			existInFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordItemExistsIn), []ast.Fc{fact.Params[2]}, fact.Line)
			err := env.storeSpecFactInMem(existInFact)
			return err
		}
		return env.newExist_St_FactPostProcess(fact)
	}

	return env.newPureFactPostProcess(fact)
}

func storeCommutativeTransitiveFact(mem map[string]*[]ast.Fc, fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
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

func (env *Env) newPureFactPostProcess(fact *ast.SpecFactStmt) error {
	// 如果是 transitive prop，那么需要更新 transitive prop mem
	if fact.TypeEnum == ast.TruePure && env.IsTransitiveProp(string(fact.PropName)) {
		if env.TransitivePropMem[string(fact.PropName)] == nil {
			env.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Fc)
		}
		env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
	}

	if glob.IsBuiltinKeywordKeySymbolCanBeFcAtomName(string(fact.PropName)) {
		if fact.PropName == glob.KeywordIn {
			return env.inFactPostProcess(fact)
		} else {
			return nil
		}
	}

	propDef := env.GetPropDef(fact.PropName)

	if propDef != nil {
		if fact.TypeEnum == ast.TruePure {
			return env.newTruePureFact_EmitFactsKnownByDef(fact)
		}
		return nil
	}

	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef != nil {
		if fact.TypeEnum == ast.TruePure {
			return nil
		} else {
			for _, thenFact := range existPropDef.DefBody.IffFacts {
				_, ok := thenFact.(*ast.SpecFactStmt)
				if !ok {
					return nil
				}
			}
			return env.newFalseExistFact_EmitEquivalentUniFact(fact)
		}
	}

	return fmt.Errorf("unknown prop %s", fact.PropName)
}

func (env *Env) newTruePureFact_EmitFactsKnownByDef(fact *ast.SpecFactStmt) error {
	propDef := env.GetPropDef(fact.PropName)
	if propDef == nil {
		// TODO 这里需要考虑prop的定义是否在当前包中。当然这里有点复杂，因为如果是内置的prop，那么可能需要到builtin包中去找
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

		if glob.RequireMsg() {
			env.Msgs = append(env.Msgs, fmt.Sprintf("%s\nis true by definition", instantiated))
		}

		if err != nil {
			return err
		}
	}

	for _, thenFact := range propDef.ThenFacts {
		instantiated, err := thenFact.Instantiate(uniMap)
		if err != nil {
			return err
		}

		err = env.newFactNoPostProcess(instantiated)

		if glob.RequireMsg() {
			env.Msgs = append(env.Msgs, fmt.Sprintf("%s\nis true by definition", instantiated))
		}

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
		return fmt.Errorf("exist fact %s has no definition", fact)
	}

	return nil
}

// have(exist ... st ...) => exist
func (env *Env) newTrueExist_St_FactPostProcess(fact *ast.SpecFactStmt) error {
	_, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, env.CurMatchEnv)
	err := env.storeSpecFactInMem(existFact)
	if err != nil {
		return err
	}

	// iff facts
	iffFacts, thenFacts, err := env.iffFactsInExistStFact(fact)
	if err != nil {
		return err
	}

	for _, iffFact := range iffFacts {
		err := env.NewFact(iffFact)
		if err != nil {
			return err
		}
	}

	for _, thenFact := range thenFacts {
		err := env.NewFact(thenFact)
		if err != nil {
			return err
		}
	}

	return nil
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, error) {
	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef == nil {
		return nil, fmt.Errorf("exist fact %s has no definition", fact)
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
			return nil, fmt.Errorf("exist fact %s has no definition", fact)
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

	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.ExistParamSets, domFacts, thenFacts, existPropDef.Line), nil
}

func (env *Env) isTrueEqualFact_StoreIt(fact *ast.SpecFactStmt) (bool, error) {
	if !fact.IsTrue() {
		return false, nil
	}

	if fact.PropName != glob.KeySymbolEqual {
		return false, nil
	}

	if len(fact.Params) != 2 {
		return true, fmt.Errorf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact)
	}

	err := storeCommutativeTransitiveFact(env.EqualMem, fact)
	if err != nil {
		return false, err
	}

	// 如果 a = b 中，某一项是 数值型，那就算出来这个数值，卷后把它保留在equalMem中
	err = env.storeSymbolValue(fact.Params[0], fact.Params[1])
	if err != nil {
		return false, err
	}

	return true, nil
}

func (env *Env) StoreTrueEqualValues(key, value ast.Fc) {
	env.SymbolValueMem[key.String()] = value
}

func (env *Env) storeSymbolValue(left, right ast.Fc) error {
	// if cmp.IsNumLitFc(left) {
	// 	env.SymbolValueMem[right.String()] = left
	// }
	// if cmp.IsNumLitFc(right) {
	// 	env.SymbolValueMem[left.String()] = right
	// }

	if ok := cmp.IsNumLitFc(left); ok {
		env.StoreTrueEqualValues(right, left)
	}

	if ok := cmp.IsNumLitFc(right); ok {
		env.StoreTrueEqualValues(left, right)
	}

	return nil
}

func (env *Env) GetEqualFcs(fc ast.Fc) (*[]ast.Fc, bool) {
	fcAsStr := fc.String()
	facts, ok := env.EqualMem[fcAsStr]
	return facts, ok
}

func (env *Env) iffFactsInExistStFact(fact *ast.SpecFactStmt) ([]ast.FactStmt, []ast.FactStmt, error) {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef == nil {
		return nil, nil, fmt.Errorf("exist fact %s has no definition", fact)
	}

	uniMap := map[string]ast.Fc{}
	for i := range existParams {
		uniMap[existPropDef.ExistParams[i]] = existParams[i]
	}

	for i := range factParams {
		uniMap[existPropDef.DefBody.DefHeader.Params[i]] = factParams[i]
	}

	instantiatedIffFacts := []ast.FactStmt{}
	// instantiate iff facts
	for _, iffFact := range existPropDef.DefBody.IffFacts {
		instantiated, err := iffFact.Instantiate(uniMap)
		if err != nil {
			return nil, nil, err
		}
		instantiatedIffFacts = append(instantiatedIffFacts, instantiated)
	}

	instantiatedThenFacts := []ast.FactStmt{}
	for _, thenFact := range existPropDef.DefBody.ThenFacts {
		instantiated, err := thenFact.Instantiate(uniMap)
		if err != nil {
			return nil, nil, err
		}
		instantiatedThenFacts = append(instantiatedThenFacts, instantiated)
	}

	return instantiatedIffFacts, instantiatedThenFacts, nil
}

func (env *Env) ExecDefFnTemplate(stmt *ast.FnTemplateDefStmt) error {
	// 确保template name 没有被声明过
	if env.IsAtomDeclared(stmt.TemplateDefHeader.Name, map[string]struct{}{}) {
		return fmt.Errorf("fn template name %s is already declared", stmt.TemplateDefHeader.Name)
	}

	err := env.AtomsInFnTemplateFnTemplateDeclared(ast.FcAtom(stmt.TemplateDefHeader.Name), stmt)
	if err != nil {
		return err
	}

	env.FnTemplateDefMem[string(stmt.TemplateDefHeader.Name)] = *stmt
	return nil
}

func (env *Env) newEnumFact(stmt *ast.EnumStmt) error {
	forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts := ast.TransformEnumToUniFact(stmt.CurSet, stmt.Items)

	err := env.NewFact(ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIn), []ast.Fc{stmt.CurSet, ast.FcAtom(glob.KeywordSet)}, stmt.Line))
	if err != nil {
		return err
	}

	err = env.NewFact(forallItemInSetEqualToOneOfGivenItems)
	if err != nil {
		return err
	}

	for _, pairwiseNotEqualFact := range pairwiseNotEqualFacts {
		err := env.NewFact(pairwiseNotEqualFact)
		if err != nil {
			return err
		}
	}

	for _, equalFact := range itemsInSetFacts {
		err := env.NewFact(equalFact)
		if err != nil {
			return err
		}
	}

	// postprocess 1. s is $is_finite_set 2. len(s) = number of items in set
	// finiteSetFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordIsFiniteSet), []ast.Fc{stmt.EnumName})
	finiteSetFact := ast.NewInFactWithFc(stmt.CurSet, ast.FcAtom(glob.KeywordFiniteSet))
	err = env.NewFact(finiteSetFact)
	if err != nil {
		return err
	}

	lengthOfSet := strconv.Itoa(len(stmt.Items))
	lengthOfSetAsFcAtom := ast.FcAtom(lengthOfSet)

	lenFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.NewFcFn(ast.FcAtom(glob.KeywordLen), []ast.Fc{stmt.CurSet}), lengthOfSetAsFcAtom}, stmt.Line)
	err = env.NewFact(lenFact)
	if err != nil {
		return err
	}

	err = env.storeFactInEnumMem(stmt)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) newIntensionalSetFact(stmt *ast.IntensionalSetStmt) error {
	leftUniFact, rightUniFact, err := stmt.ToEquivalentUniFacts()
	if err != nil {
		return err
	}

	if err = env.NewFact(leftUniFact); err != nil {
		return err
	}

	if err = env.NewFact(rightUniFact); err != nil {
		return err
	}

	env.IntensionalSetMem[stmt.CurSet.String()] = *stmt

	return nil
}

func (env *Env) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFact *ast.SpecFactStmt) error {
	return env.storeUniFact(thenFact, stmt)
}

func (env *Env) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) error {
	return env.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
}

func (env *Env) newUniFact_ThenFactIsEnumStmt(stmt *ast.UniFactStmt, thenFact *ast.EnumStmt) error {
	forallItemInSetEqualToOneOfGivenItems, pairwiseNotEqualFacts, itemsInSetFacts := ast.TransformEnumToUniFact(thenFact.CurSet, thenFact.Items)
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, forallItemInSetEqualToOneOfGivenItems)
	err := env.newUniFact(mergedUniFact)
	if err != nil {
		return err
	}
	for _, fact := range pairwiseNotEqualFacts {
		err := env.storeUniFact(fact, stmt)
		if err != nil {
			return err
		}
	}
	for _, fact := range itemsInSetFacts {
		err := env.storeUniFact(fact, stmt)
		if err != nil {
			return err
		}
	}

	return nil
}

func (env *Env) newUniFact_ThenFactIsIntensionalSetStmt(stmt *ast.UniFactStmt, thenFact *ast.IntensionalSetStmt) error {
	leftUniFact, rightUniFact, err := thenFact.ToEquivalentUniFacts()
	if err != nil {
		return err
	}

	mergedLeftUniFact := ast.MergeOuterInnerUniFacts(stmt, leftUniFact)
	if err := env.newUniFact(mergedLeftUniFact); err != nil {
		return err
	}

	mergedRightUniFact := ast.MergeOuterInnerUniFacts(stmt, rightUniFact)
	if err := env.newUniFact(mergedRightUniFact); err != nil {
		return err
	}

	return nil
}

func (env *Env) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) error {
	thenToIff := thenFact.NewUniFactWithThenToIff()
	iffToThen := thenFact.NewUniFactWithIffToThen()

	mergedThenToIff := ast.MergeOuterInnerUniFacts(stmt, thenToIff)
	if err := env.newUniFact(mergedThenToIff); err != nil {
		return err
	}

	mergedIffToThen := ast.MergeOuterInnerUniFacts(stmt, iffToThen)
	if err := env.newUniFact(mergedIffToThen); err != nil {
		return err
	}

	return nil
}

func (env *Env) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) error {
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
	return env.newUniFact(mergedUniFact)
}

func (env *Env) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) error {
	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()
	for _, equalFact := range equalFacts {
		err := env.newUniFact_ThenFactIsSpecFact(stmt, equalFact)
		if err != nil {
			return err
		}
	}
	return nil
}

func (env *Env) storeFactInEnumMem(stmt *ast.EnumStmt) error {
	env.EnumFacts[stmt.CurSet.String()] = stmt.Items
	return nil
}

func (env *Env) storeSpecFactInMem(stmt *ast.SpecFactStmt) error {
	err := env.KnownFactsStruct.SpecFactMem.newFact(stmt)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) storeLogicFact(stmt *ast.OrStmt) error {
	err := env.KnownFactsStruct.SpecFactInLogicExprMem.newFact(stmt)
	if err != nil {
		return nil
	}

	return nil
}

func (env *Env) storeUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) error {
	err := env.KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) newEqualsFact(stmt *ast.EqualsFactStmt) error {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		err := env.NewFact(equalFact)
		if err != nil {
			return err
		}
	}
	return nil
}

func (env *Env) newEqualsFactNoPostProcess(stmt *ast.EqualsFactStmt) error {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		err := env.newSpecFactNoPostProcess(equalFact)
		if err != nil {
			return err
		}
	}
	return nil
}
