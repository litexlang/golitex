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
		return env.NewSpecFact(f)
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

func (env *Env) NewSpecFact(fact *ast.SpecFactStmt) error {
	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeywordCommutativeProp) {
		// 验证它的def确实只有两个元素
		if len(fact.Params) != 1 {
			return fmt.Errorf("commutative prop is supposed to have one parameter, but %s has %d parameters", fact.PropName, len(fact.Params))
		}

		propNameAsAtom, ok := fact.Params[0].(*ast.FcAtom)
		if !ok {
			return fmt.Errorf("commutative prop is supposed to have one atom parameter, but %s has %s", fact.PropName, fact.Params[0])
		}

		propDef, ok := env.PropMem.Get(*propNameAsAtom)
		if !ok {
			return fmt.Errorf("prop %s has no definition", fact.PropName)
		}

		if len(propDef.DefHeader.Params) != 2 {
			return fmt.Errorf("prop %s is supposed to be commutative, but has no %d parameters", fact.PropName, len(propDef.DefHeader.Params))
		}

		env.InsertCommutativeProp(*propNameAsAtom)

		return nil
	}

	if ast.IsFcAtom_HasGivenName_EmptyPkgName(&fact.PropName, glob.KeySymbolEqual) {
		err := env.NewEqualFact(fact)
		if err != nil {
			return err
		}
		return nil
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

func (env *Env) newAtomSpecFactPostProcess(fact *ast.SpecFactStmt) error {
	if fact.TypeEnum == ast.TrueAtom {
		if glob.KnowSpecFactByDef {
			return env.emit_specFact_DefFacts(fact)
		} else {
			return nil
		}
	} else {
		return nil
	}
}

func (env *Env) emit_specFact_DefFacts(fact *ast.SpecFactStmt) error {
	propDef, ok := env.PropMem.Get(fact.PropName)
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
		_, ok := curEnv.ObjMem.Dict[glob.BtEmptyPkgName][name]
		if ok {
			return duplicateDefMsg(glob.BtEmptyPkgName, name, glob.KeywordObj)
		}
		_, ok = curEnv.FnMem.Dict[glob.BtEmptyPkgName][name]
		if ok {
			return duplicateDefMsg(glob.BtEmptyPkgName, name, glob.KeywordFn)
		}
		_, ok = curEnv.PropMem.Dict[glob.BtEmptyPkgName][name]
		if ok {
			return duplicateDefMsg(glob.BtEmptyPkgName, name, glob.KeywordProp)
		}
	}

	return nil
}

func (env *Env) NewDefProp(stmt *ast.DefPropStmt) error {
	err := env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.PropMem.Insert(stmt, glob.BtEmptyPkgName)
}

func (env *Env) NewDefObj(stmt *ast.DefObjStmt) error {
	for _, objName := range stmt.Objs {
		err := env.IsInvalidName(objName)
		if err != nil {
			return err
		}
	}

	return env.ObjMem.Insert(stmt, glob.BtEmptyPkgName)
}

func (env *Env) NewDefFn(stmt *ast.DefFnStmt) error {
	err := env.IsInvalidName(stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.FnMem.Insert(stmt, glob.BtEmptyPkgName)
}

func (env *Env) NewDefExistProp(stmt *ast.DefExistPropStmt) error {
	err := env.IsInvalidName(stmt.Def.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropMem.Insert(stmt, glob.BtEmptyPkgName)
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.UniFactStmt, error) {
	if fact.TypeEnum != ast.FalseExist {
		return nil, fmt.Errorf("exist fact must have one parameter")
	}

	existPropDef, ok := env.ExistPropMem.Get(fact.PropName)
	if !ok {
		return nil, fmt.Errorf("exist fact %s has no definition", fact.String())
	}

	uniMap := map[string]ast.Fc{}
	for i, propParam := range existPropDef.Def.DefHeader.Params {
		uniMap[propParam] = fact.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, domFact := range existPropDef.Def.DomFacts {
		instantiated, err := domFact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		domFacts = append(domFacts, instantiated)
	}

	specThenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range existPropDef.Def.IffFacts {
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

	return ast.NewUniFactStmtWithSetReqInDom(existPropDef.ExistParams, existPropDef.ExistParamSets, domFacts, thenFacts, ast.EmptyIffFacts), nil
}

func (env *Env) NewEqualFact(fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("`=` fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFacts, leftGot := env.EqualMem[leftAsStr]
	storedEqualRightFacts, rightGot := env.EqualMem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFacts == storedEqualRightFacts {
			return nil
		} else {
			newEqualFacts := []ast.Fc{}
			newEqualFacts = append(newEqualFacts, *storedEqualLeftFacts...)
			newEqualFacts = append(newEqualFacts, *storedEqualRightFacts...)
			*storedEqualLeftFacts = newEqualFacts
			*storedEqualRightFacts = newEqualFacts
			return nil
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFacts = append(*storedEqualLeftFacts, fact.Params[1])
		env.EqualMem[rightAsStr] = storedEqualLeftFacts
		return nil
	}

	if !leftGot && rightGot {
		*storedEqualRightFacts = append(*storedEqualRightFacts, fact.Params[0])
		env.EqualMem[leftAsStr] = storedEqualRightFacts
		return nil
	}

	if !leftGot && !rightGot {
		newEqualFacts := []ast.Fc{fact.Params[0], fact.Params[1]}
		env.EqualMem[leftAsStr] = &newEqualFacts
		env.EqualMem[rightAsStr] = &newEqualFacts
		return nil
	}

	return nil
}

func (env *Env) GetEqualFact(fc ast.Fc) (*[]ast.Fc, bool) {
	fcAsStr := fc.String()
	facts, ok := env.EqualMem[fcAsStr]
	return facts, ok
}
