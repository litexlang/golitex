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

func (env *Env) NewFact(stmt ast.FactStmt) glob.GlobRet {
	// 检查是否符合要求：比如涉及到的符号是否都定义了
	if ret := env.AtomObjsInFactProperlyDefined(stmt, map[string]struct{}{}); ret.IsNotTrue() {
		return glob.NewGlobErr(stmt.String()).AddMsg(ret.String())
	}

	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFact(f)
	case *ast.OrStmt:
		return env.newLogicExprFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFact(f)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

// NewFactWithDeclarationCheck checks if all atoms in the fact are declared, and if so, calls NewFact.
// Returns an error if any atoms are undeclared or if NewFact fails.
func (env *Env) NewFactWithDeclarationCheck(fact ast.FactStmt) glob.GlobRet {
	ret := env.AtomObjsInFactProperlyDefined(fact, map[string]struct{}{})
	if ret.IsErr() {
		return ret
	}
	return env.NewFact(fact)
}

func (env *Env) newSpecFactNoPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	// if env.CurMatchProp == nil {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return env.isTrueEqualFact_StoreIt(fact)
	}
	// }

	// if isMathInductionProp, err := env.isMathInductionPropName_StoreIt(fact); err != nil {
	// 	return err
	// } else if isMathInductionProp {
	// 	return nil
	// }

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(fact, env.CurMatchEnv)
	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

// 为了防止 p 的定义中推导出q，q的定义中推导出p，导致循环定义，所以需要这个函数
// ? 总觉得这里的 除了 spec fact 以外，其他fact 的定义中推导出p，p的定义中推导出其他fact，也可能导致循环
func (env *Env) newFactNoPostProcess(stmt ast.FactStmt) glob.GlobRet {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFactNoPostProcess(f)
	case *ast.OrStmt:
		return env.newLogicExprFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFactNoPostProcess(f)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

func (env *Env) newLogicExprFact(fact *ast.OrStmt) glob.GlobRet {
	ret := env.KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
	return ret
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) glob.GlobRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return env.isTrueEqualFact_StoreIt(fact)
	}

	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	// postprocess
	var postProcessRet glob.GlobRet
	if fact.IsExist_St_Fact() {
		postProcessRet = env.newExist_St_FactPostProcess(fact)
	} else {
		postProcessRet = env.newPureFactPostProcess(fact)
	}

	if postProcessRet.IsErr() {
		return postProcessRet
	}

	// Return derived facts from post-processing
	return postProcessRet
}

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

func (env *Env) newPureFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	// 如果是 transitive prop，那么需要更新 transitive prop mem
	if fact.TypeEnum == ast.TruePure && env.IsTransitiveProp(string(fact.PropName)) {
		if env.TransitivePropMem[string(fact.PropName)] == nil {
			env.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Obj)
		}
		env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
	}

	if glob.IsBuiltinPropName(string(fact.PropName)) || glob.IsBuiltinExistPropName(string(fact.PropName)) {
		ret := env.BuiltinPropExceptEqualPostProcess(fact)
		// Inherit derived facts from builtin prop post-processing
		return ret
	}

	propDef := env.GetPropDef(fact.PropName)

	if propDef != nil {
		if fact.TypeEnum == ast.TruePure {
			ret := env.newTruePureFact_EmitFactsKnownByDef(fact)
			// Inherit derived facts from prop definition
			return ret
		}
		return glob.NewGlobTrue("")
	}

	existPropDef := env.GetExistPropDef(fact.PropName)
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
			ret := env.newFalseExistFact_EmitEquivalentUniFact(fact)
			// Inherit derived facts from exist prop processing
			return ret
		}
	}

	return glob.ErrRet(fmt.Errorf("undefined prop: %s", fact.PropName))
}

// equalSetFactPostProcess handles postprocessing for equal_set(a, b) facts
// It creates an equality fact a = b
func (env *Env) equalSetFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	derivedFacts := []string{}

	// Create a = b fact
	equalFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := env.NewFact(equalFact)
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
func (env *Env) equalTupleFactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 3 {
		return glob.ErrRet(fmt.Errorf("equal_tuple fact expect 3 parameters, get %d in %s", len(fact.Params), fact))
	}

	equalFact := ast.NewEqualFact(fact.Params[0], fact.Params[1])

	ret := env.NewFact(equalFact)
	if ret.IsErr() {
		return ret
	}

	return ret
}

func (env *Env) newTruePureFact_EmitFactsKnownByDef(fact *ast.SpecFactStmt) glob.GlobRet {
	// 通过 prop 定义中的 iff 和 implication 规则，推导出后续结论
	// 因为 prop 的定义包含了 iff（当且仅当）和 implication（蕴含）关系，
	// 所以当该 prop 为真时，可以推导出定义中指定的后续事实
	propDef := env.GetPropDef(fact.PropName)
	if propDef == nil {
		// TODO 这里需要考虑prop的定义是否在当前包中。当然这里有点复杂，因为如果是内置的prop，那么可能需要到builtin包中去找
		return glob.NewGlobTrue("")
	}

	iffFacts := []string{}
	implicationFacts := []string{}

	uniMap := map[string]ast.Obj{}
	for i, propParam := range propDef.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	// 通过 iff（当且仅当）规则推导出的事实
	for _, thenFact := range propDef.IffFactsOrNil {
		instantiated, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}

		ret := env.newFactNoPostProcess(instantiated)

		// Note: Messages are now added to ExecRet in the caller, not to env.Msgs

		if ret.IsErr() {
			return ret
		}

		// Collect the instantiated fact itself as a derived fact
		if ret.IsTrue() {
			if specFact, ok := instantiated.(*ast.SpecFactStmt); ok {
				iffFacts = append(iffFacts, specFact.String())
			} else {
				iffFacts = append(iffFacts, instantiated.String())
			}
		}
	}

	// 通过 implication（蕴含）规则推导出的事实
	for _, thenFact := range propDef.ImplicationFactsOrNil {
		instantiated, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err)
		}

		ret := env.newFactNoPostProcess(instantiated)

		// Note: Messages are now added to ExecRet in the caller, not to env.Msgs

		if ret.IsErr() {
			return ret
		}

		// Collect the instantiated fact itself as a derived fact
		if ret.IsTrue() {
			implicationFacts = append(implicationFacts, instantiated.String())
		}
	}

	// 构建返回消息，明确标注哪些来自 iff，哪些来自 implication
	derivedFacts := []string{}
	if len(iffFacts) > 0 || len(implicationFacts) > 0 {
		derivedFacts = append(derivedFacts, fmt.Sprintf("derive facts from %s:", fact.String()))
		derivedFacts = append(derivedFacts, iffFacts...)
		derivedFacts = append(derivedFacts, implicationFacts...)
		derivedFacts = append(derivedFacts, "")
	}

	return glob.NewGlobTrueWithMsgs(derivedFacts)
}

func (env *Env) newExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	if fact.TypeEnum == ast.TrueExist_St {
		return env.newTrueExist_St_FactPostProcess(fact)
	} else {
		return glob.NewGlobTrue("")
	}
}

// not exist => forall not
func (env *Env) newFalseExistFact_EmitEquivalentUniFact(fact *ast.SpecFactStmt) glob.GlobRet {
	uniFact, ret := env.NotExistToForall(fact)
	if ret.IsErr() {
		return ret
	}

	ret = env.newFactNoPostProcess(uniFact)

	if ret.IsErr() {
		return glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	return glob.NewGlobTrue("")
}

// have(exist ... st ...) => exist
func (env *Env) newTrueExist_St_FactPostProcess(fact *ast.SpecFactStmt) glob.GlobRet {
	existParams, factParams := ast.GetExistFactExistParamsAndFactParams(fact)

	existFact := ast.NewSpecFactStmt(ast.TruePure, fact.PropName, factParams, fact.Line)

	// err := env.KnownFacts.SpecFactMem.NewFactInSpecFactMem(existFact, env.CurMatchEnv)
	if fact.PropName == glob.KeywordItemExistsIn {
		ret := env.storeSpecFactInMem(existFact)
		if ret.IsErr() {
			return ret
		}
		inFact := ast.NewInFactWithObj(existParams[0], factParams[0])
		ret = env.NewFact(inFact)
		if ret.IsErr() {
			return ret
		}
		return glob.NewGlobTrue("")
	}

	ret := env.storeSpecFactInMem(existFact)
	if ret.IsErr() {
		return ret
	}

	// iff facts
	iffFacts, thenFacts, ret := env.iffFactsInExistStFact(fact)
	if ret.IsErr() {
		return ret
	}

	for _, iffFact := range iffFacts {
		ret := env.NewFact(iffFact)
		if ret.IsErr() {
			return ret
		}
	}

	for _, thenFact := range thenFacts {
		ret := env.NewFact(thenFact)
		if ret.IsErr() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, glob.GlobRet) {
	existPropDef := env.GetExistPropDef(fact.PropName)
	if existPropDef == nil {
		return nil, glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
	}

	uniMap := map[string]ast.Obj{}
	for i, propParam := range existPropDef.DefBody.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, domFact := range existPropDef.DefBody.DomFactsOrNil {
		instantiated, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return nil, glob.ErrRet(err)
		}
		domFacts = append(domFacts, instantiated)
	}

	specThenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range existPropDef.DefBody.IffFactsOrNil {
		asSpecFactStmt, ok := thenFact.(*ast.SpecFactStmt)
		if !ok {
			return nil, glob.ErrRet(fmt.Errorf("exist fact %s has no definition", fact))
		}

		reversedFacts := asSpecFactStmt.ReverseIsTrue()
		for _, reversedFact := range reversedFacts {
			instantiated, err := reversedFact.InstantiateFact(uniMap)
			if err != nil {
				return nil, glob.ErrRet(err)
			}
			specThenFacts = append(specThenFacts, instantiated.(*ast.SpecFactStmt))
		}
	}

	thenFacts := []ast.FactStmt{}
	for _, specThenFact := range specThenFacts {
		thenFacts = append(thenFacts, specThenFact)
	}

	return ast.NewUniFact(existPropDef.ExistParams, existPropDef.ExistParamSets, domFacts, thenFacts, existPropDef.Line), glob.NewGlobTrue("")
}

func (env *Env) isTrueEqualFact_StoreIt(fact *ast.SpecFactStmt) glob.GlobRet {
	if len(fact.Params) != 2 {
		return glob.ErrRet(fmt.Errorf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	ret := storeCommutativeTransitiveFact(env.EqualMem, fact)
	if ret.IsErr() {
		return ret
	}

	// 如果 a = b 中，某一项是 数值型，那就算出来这个数值，卷后把它保留在equalMem中
	ret = env.storeSymbolSimplifiedValue(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// postprocess for cart: if x = cart(x1, x2, ..., xn)
	if cart, ok := fact.Params[1].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cart.FnHead, glob.KeywordCart) {
		ret = env.equalFactPostProcess_cart(fact)
		if ret.IsErr() {
			return ret
		}
	}

	// 处理 tuple 相等的情况
	ret = env.equalFactPostProcess_tupleEquality(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 处理 x = {1, 2, 3} 的情况
	ret = env.equalFactPostProcess_listSetEquality(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	// 处理 x = {x Z: x > 5} 的情况
	// ret = env.equalFactPostProcess_SetBuilderEquality(fact.Params[0], fact.Params[1])
	// if ret.IsErr() {
	// 	return ret
	// }

	return glob.NewGlobTrue("")
}

func (env *Env) StoreTrueEqualValues(key, value ast.Obj) {
	// 如果已经知道它的值了，那不能存了；否则比如我在外部环境里知道了a = 3，内部环境在反证法证明 a != 1，那我 a = 1就把a = 3覆盖掉了，a = 3这个取值貌似就不work了。某种程度上就是弄了个const
	if v := env.GetSymbolSimplifiedValue(key); v != nil {
		return
	}
	env.SymbolSimplifiedValueMem[key.String()] = value
}

func simplifyNumExprObj(obj ast.Obj) ast.Obj {
	simplifiedNumExprObj := cmp.IsNumExprObjThenSimplify(obj)
	return simplifiedNumExprObj
}

func (env *Env) storeSymbolSimplifiedValue(left, right ast.Obj) glob.GlobRet {
	_, newLeft := env.ReplaceSymbolWithValue(left)
	if cmp.IsNumExprLitObj(newLeft) {
		simplifiedNewLeft := simplifyNumExprObj(newLeft)
		env.StoreTrueEqualValues(right, simplifiedNewLeft)
	}

	_, newRight := env.ReplaceSymbolWithValue(right)
	if cmp.IsNumExprLitObj(newRight) {
		simplifiedNewRight := simplifyNumExprObj(newRight)
		env.StoreTrueEqualValues(left, simplifiedNewRight)
	}

	return glob.NewGlobTrue("")
}

func (env *Env) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := env.EqualMem[objAsStr]
	return facts, ok
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

func (env *Env) ExecDefFnTemplate(stmt *ast.FnTemplateDefStmt) glob.GlobRet {
	// 确保template name 没有被声明过
	ret := env.IsNameDefinedOrBuiltin(string(stmt.TemplateDefHeader.Name), map[string]struct{}{})
	if ret.IsTrue() {
		return glob.ErrRet(fmt.Errorf("fn template name %s is already declared", stmt.TemplateDefHeader.Name))
	}

	ret = env.AtomsInFnTemplateFnTemplateDeclared(ast.Atom(stmt.TemplateDefHeader.Name), stmt)
	if ret.IsErr() {
		return ret
	}

	env.FnTemplateDefMem[string(stmt.TemplateDefHeader.Name)] = *stmt
	return glob.NewGlobTrue("")
}

func (env *Env) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFact *ast.SpecFactStmt) glob.GlobRet {
	return env.storeUniFact(thenFact, stmt)
}

func (env *Env) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) glob.GlobRet {
	return env.KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
}

func (env *Env) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) glob.GlobRet {
	thenToIff := thenFact.NewUniFactWithThenToIff()
	iffToThen := thenFact.NewUniFactWithIffToThen()

	mergedThenToIff := ast.MergeOuterInnerUniFacts(stmt, thenToIff)
	ret := env.newUniFact(mergedThenToIff)
	if ret.IsErr() {
		return ret
	}

	mergedIffToThen := ast.MergeOuterInnerUniFacts(stmt, iffToThen)
	ret = env.newUniFact(mergedIffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (env *Env) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) glob.GlobRet {
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
	return env.newUniFact(mergedUniFact)
}

func (env *Env) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) glob.GlobRet {
	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()
	for _, equalFact := range equalFacts {
		ret := env.newUniFact_ThenFactIsSpecFact(stmt, equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

// func (env *Env) storeFactInEnumMem(stmt *ast.EnumStmt) glob.GlobRet {
// 	env.EnumFacts[stmt.CurSet.String()] = stmt.Items
// 	return glob.NewGlobTrue("")
// }

func (env *Env) storeSpecFactInMem(stmt *ast.SpecFactStmt) glob.GlobRet {
	ret := env.KnownFactsStruct.SpecFactMem.newFact(stmt)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (env *Env) storeUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) glob.GlobRet {
	ret := env.KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (env *Env) newEqualsFact(stmt *ast.EqualsFactStmt) glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := env.NewFact(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

func (env *Env) newEqualsFactNoPostProcess(stmt *ast.EqualsFactStmt) glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := env.newSpecFactNoPostProcess(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}
