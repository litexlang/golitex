// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_memory

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	mem "golitex/litex_memory"
)

func (env *Env) NewFact(stmt ast.FactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.NewSpecFact(f)
	case *ast.CondFactStmt:
		return env.NewCondFact(f)
	case *ast.ConUniFactStmt:
		return env.NewUniFact(f)
	case *ast.LogicExprStmt:
		return env.NewLogicExprStmt(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) NewLogicExprStmt(fact *ast.LogicExprStmt) error {
	return env.SpecFactMem.InsertSpecFactUnderLogicExpr(fact)
}

func (env *Env) NewSpecFact(fact *ast.SpecFactStmt) error {
	if fact.IsEqualFact() {
		return env.NewEqualFact(fact)
	}

	err := env.SpecFactMem.InsertSpecFact(fact)
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
		return env.newTrueAtomSpecFactPostProcess(fact)
	} else {
		return nil
	}
}

func (env *Env) newTrueAtomSpecFactPostProcess(fact *ast.SpecFactStmt) error {
	propDef, ok := env.PropMem.Get(fact.PropName)
	if !ok {
		return nil

		// TODO 这里需要考虑prop的定义是否在当前包中
		// return fmt.Errorf("prop %s has no definition", fact.PropName)
	}

	uniConMap := map[string]ast.Fc{}
	for i, propParam := range propDef.DefHeader.Params {
		uniConMap[propParam] = fact.Params[i]
	}

	for _, thenFact := range propDef.IffFacts {
		instantiated, err := thenFact.Instantiate(uniConMap)
		if err != nil {
			return err
		}

		// TODO: 这里不只插入到SpecFactMem中，还要插入任何mem，因为现在iff非常的复杂，所有情况都行
		err = env.SpecFactMem.InsertSpecFact(instantiated.(*ast.SpecFactStmt))
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
	conUniFact, err := env.NotExistToForall(fact)
	if err != nil {
		return err
	}

	err = env.UniFactMem.Insert(conUniFact)
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

	err := env.SpecFactMem.InsertSpecFact(existFact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) NewEqualFact(stmt *ast.SpecFactStmt) error {
	left := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[0],
		Values:  &[]ast.Fc{stmt.Params[1]},
	}

	right := &mem.EqualFactMemoryTreeNode{
		FcAsKey: stmt.Params[1],
		Values:  &[]ast.Fc{stmt.Params[0]},
	}

	leftSearched, err := env.EqualFactMem.Mem.TreeSearch(left)
	if err != nil {
		return err
	}
	rightSearched, err := env.EqualFactMem.Mem.TreeSearch(right)
	if err != nil {
		return err
	}

	if leftSearched != nil && rightSearched != nil {
		if leftSearched == rightSearched {
			return nil
		} else {
			*leftSearched.Key.Values = append(*leftSearched.Key.Values, *rightSearched.Key.Values...)
			rightSearched.Key.Values = leftSearched.Key.Values
		}
	} else if leftSearched == nil && rightSearched != nil {
		*rightSearched.Key.Values = append(*rightSearched.Key.Values, stmt.Params[0])
		left.Values = rightSearched.Key.Values
		env.EqualFactMem.Mem.Insert(left) // 让树中有这个key
	} else if leftSearched != nil && rightSearched == nil {
		*leftSearched.Key.Values = append(*leftSearched.Key.Values, stmt.Params[1])
		right.Values = leftSearched.Key.Values
		env.EqualFactMem.Mem.Insert(right)
	} else if leftSearched == nil && rightSearched == nil {
		equalSlice := &[]ast.Fc{stmt.Params[0], stmt.Params[1]}
		env.EqualFactMem.Mem.Insert(left)
		env.EqualFactMem.Mem.Insert(right)
		left.Values = equalSlice
		right.Values = equalSlice
	}

	return nil
}

func (env *Env) NewCondFact(fact *ast.CondFactStmt) error {
	err := env.CondFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) NewUniFact(fact *ast.ConUniFactStmt) error {
	err := env.UniFactMem.Insert(fact)
	if err != nil {
		return err
	}
	return nil
}

func (env *Env) IsInvalidName(pkgName string, name string) error {
	err := glob.IsValidName(name)
	if err != nil {
		return err
	}

	for curEnv := env; curEnv != nil; curEnv = curEnv.Parent {
		_, ok := curEnv.ObjMem.Dict[pkgName][name]
		if ok {
			return duplicateDefMsg(pkgName, name, glob.KeywordObj)
		}
		_, ok = curEnv.FnMem.Dict[pkgName][name]
		if ok {
			return duplicateDefMsg(pkgName, name, glob.KeywordFn)
		}
		_, ok = curEnv.PropMem.Dict[pkgName][name]
		if ok {
			return duplicateDefMsg(pkgName, name, glob.KeywordProp)
		}
	}

	return nil
}

func (env *Env) Declare(stmt ast.Stmt, name string) error {
	// TODO: 声明obj，也可能是fn，甚至可能是prop
	return nil
}

func (env *Env) IsSpecFactPropCommutative(fact *ast.SpecFactStmt) bool {
	if len(fact.Params) != 2 {
		return false
	}
	return env.isPropCommutative(&fact.PropName)
}

func (env *Env) isPropCommutative(opt ast.Fc) bool {
	if ast.IsEqualOptFc(opt) {
		return true
	}

	// TODO
	_ = opt
	return false
}

func (env *Env) NewDefConProp(stmt *ast.DefConPropStmt, pkgName string) error {
	err := env.IsInvalidName(pkgName, stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.PropMem.Insert(stmt, pkgName)
}

func (env *Env) NewDefObj(stmt *ast.DefObjStmt, pkgName string) error {
	for _, objName := range stmt.Objs {
		err := env.IsInvalidName(pkgName, objName)
		if err != nil {
			return err
		}
	}

	return env.ObjMem.Insert(stmt, pkgName)
}

func (env *Env) NewDefFn(stmt *ast.DefConFnStmt, pkgName string) error {
	err := env.IsInvalidName(pkgName, stmt.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.FnMem.Insert(stmt, pkgName)
}

func (env *Env) NewDefConExistProp(stmt *ast.DefConExistPropStmt, pkgName string) error {
	err := env.IsInvalidName(pkgName, stmt.Def.DefHeader.Name)
	if err != nil {
		return err
	}

	return env.ExistPropMem.Insert(stmt, pkgName)
}

func (env *Env) NotExistToForall(fact *ast.SpecFactStmt) (*ast.ConUniFactStmt, error) {
	if fact.TypeEnum != ast.FalseExist {
		return nil, fmt.Errorf("exist fact must have one parameter")
	}

	existPropDef, ok := env.ExistPropMem.Get(fact.PropName)
	if !ok {
		return nil, fmt.Errorf("exist fact %s has no definition", fact.String())
	}

	uniConMap := map[string]ast.Fc{}
	for i, propParam := range existPropDef.Def.DefHeader.Params {
		uniConMap[propParam] = fact.Params[i]
	}

	domFacts := []ast.FactStmt{}
	for _, domFact := range existPropDef.Def.DomFacts {
		instantiated, err := domFact.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		domFacts = append(domFacts, instantiated)
	}

	specThenFacts := []*ast.SpecFactStmt{}
	for _, thenFact := range existPropDef.Def.IffFacts {
		reversed := thenFact.ReverseIsTrue()
		instantiated, err := reversed.Instantiate(uniConMap)
		if err != nil {
			return nil, err
		}
		specThenFacts = append(specThenFacts, instantiated.(*ast.SpecFactStmt))
	}

	thenFacts := []ast.FactStmt{}
	for _, specThenFact := range specThenFacts {
		thenFacts = append(thenFacts, specThenFact)
	}

	return ast.NewConUniFactStmt(existPropDef.ExistParams, existPropDef.ExistParamSets, domFacts, thenFacts), nil
}
