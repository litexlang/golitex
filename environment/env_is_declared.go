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
	"strings"
)

func (e *Env) IsAtomDefinedByUser(AtomObjName ast.Atom) bool {
	// 如果 atom 里有 ::，那另外检查
	if strings.Contains(string(AtomObjName), glob.PkgNameAtomSeparator) {
		PkgNameAndAtomName := strings.Split(string(AtomObjName), glob.PkgNameAtomSeparator)
		PkgName := PkgNameAndAtomName[0]
		AtomName := PkgNameAndAtomName[1]
		pkgPath, ok := e.PackageManager.PkgPathNameMgr.GetPathByName(PkgName)
		if !ok {
			return false
		}
		pkgPathEnv, ok := e.PackageManager.PkgPathEnvPairs[pkgPath]
		if !ok {
			return false
		}
		ok = pkgPathEnv.isAtomDefinedAtCurEnv(ast.Atom(AtomName))
		if ok {
			return true
		}
		return ok
	}

	for env := e; env != nil; env = env.Parent {
		ok := env.isAtomDefinedAtCurEnv(AtomObjName)
		if ok {
			return true
		}
	}
	return false
}

// 其实最好要分类：有可能是obj，有可能是prop，不能在验证obj的时候验证是prop
func (e *Env) isAtomDefinedAtCurEnv(AtomObjName ast.Atom) bool {
	_, ok := e.PropDefMem[string(AtomObjName)]
	if ok {
		return true
	}

	_, ok = e.ExistPropDefMem[string(AtomObjName)]
	if ok {
		return true
	}

	_, ok = e.ObjDefMem[string(AtomObjName)]
	if ok {
		return true
	}

	_, ok = e.FnTemplateDefMem[string(AtomObjName)]

	return ok
}

func (e *Env) AreAtomsInObjDefined(obj ast.Obj, extraAtomNames map[string]struct{}) glob.GlobRet {
	if !ast.IsSetBuilder(obj) {
		atoms := ast.GetAtomsInObj(obj)
		return e.AreAtomsDeclared(atoms, extraAtomNames)
	} else {
		return e.AreAtomsInSetBuilderAreDeclared(obj.(*ast.FnObj), extraAtomNames)
	}
}

// AreAtomsInSetBuilderAreDeclared checks if all atoms in an set builder are declared,
// excluding the set builder's own parameter (which is a free variable not in the environment).
func (e *Env) AreAtomsInSetBuilderAreDeclared(obj *ast.FnObj, extraAtomNames map[string]struct{}) glob.GlobRet {
	setBuilderStruct, err := obj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(fmt.Errorf("failed to parse set builder: %s", err))
	}

	// Create a copy of extraAtomNames and add the set builder's param to it
	// This param is a free variable, so we exclude it from the declaration check
	paramExcludedNames := glob.CopyMap(extraAtomNames)
	paramExcludedNames[setBuilderStruct.Param] = struct{}{}

	// Check atoms in parentSet (excluding the param)
	ret := e.AreAtomsInObjDefined(setBuilderStruct.ParentSet, paramExcludedNames)
	if ret.IsErr() {
		ret.AddMsg(fmt.Sprintf("in parent set of set builder with param %s", setBuilderStruct.Param))
		return ret
	}

	// Check atoms in facts (excluding the param)
	for i, fact := range setBuilderStruct.Facts {
		ret := e.AreAtomsInFactAreDeclared(fact, paramExcludedNames)
		if ret.IsErr() {
			ret.AddMsg(fmt.Sprintf("in fact %d of set builder with param %s", i, setBuilderStruct.Param))
			return ret
		}
	}

	return glob.TrueRet("")
}

// TODO 来自上层的时候，有时候如果fact是uniFact，那传来的extraAtomNames里已经有uniParam了，这其实是浪费计算了
func (e *Env) AreAtomsInFactAreDeclared(fact ast.FactStmt, extraAtomNames map[string]struct{}) glob.GlobRet {
	switch asStmt := fact.(type) {
	case *ast.UniFactStmt:
		for _, param := range asStmt.Params {
			extraAtomNames[param] = struct{}{}
		}
		for _, dom := range asStmt.DomFacts {
			ret := e.AreAtomsInFactAreDeclared(dom, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}
		for _, then := range asStmt.ThenFacts {
			ret := e.AreAtomsInFactAreDeclared(then, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}
		return glob.TrueRet("")
	case *ast.UniFactWithIffStmt:
		for _, param := range asStmt.UniFact.Params {
			extraAtomNames[param] = struct{}{}
		}
		for _, dom := range asStmt.UniFact.DomFacts {
			ret := e.AreAtomsInFactAreDeclared(dom, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}

		for _, then := range asStmt.UniFact.ThenFacts {
			ret := e.AreAtomsInFactAreDeclared(then, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}

		for _, iff := range asStmt.IffFacts {
			ret := e.AreAtomsInFactAreDeclared(iff, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}
		return glob.TrueRet("")
	case *ast.SpecFactStmt:
		for _, param := range asStmt.Params {
			ret := e.AreAtomsInObjDefined(param, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}
		return glob.TrueRet("")
	case *ast.OrStmt:
		for _, fact := range asStmt.Facts {
			ret := e.AreAtomsInFactAreDeclared(fact, extraAtomNames)
			if ret.IsErr() {
				return ret
			}
		}
		return glob.TrueRet("")
	default:
		return glob.ErrRet(fmt.Errorf("unexpected fact statement type: %T", asStmt))
	}
}

func (e *Env) AreAtomsDeclared(atoms []ast.Atom, extraAtomNames map[string]struct{}) glob.GlobRet {
	for _, atom := range atoms {
		ret := e.IsAtomDeclared(atom, extraAtomNames)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.TrueRet("")
}

func (e *Env) IsAtomDeclared(atom ast.Atom, extraAtomNames map[string]struct{}) glob.GlobRet {
	// 如果是内置的符号，那就声明了
	if glob.IsBuiltinObjOrPropName(string(atom)) {
		return glob.TrueRet("")
	}

	// 如果是数字，那就声明了
	if _, ok := ast.IsNumLitAtomObj(atom); ok {
		return glob.TrueRet("")
	}

	ok := e.IsAtomDefinedByUser(atom)
	if ok {
		return glob.TrueRet("")
	}

	_, ok = extraAtomNames[string(atom)]

	if ok {
		return glob.TrueRet("")
	}

	// atom 未定义，返回错误并记录 atom 名称
	return glob.ErrRet(fmt.Errorf("%s is not defined", atom))
}

func (e *Env) ThereIsNoDuplicateObjNamesAndAllAtomsInParamSetsAreDefined(params []string, setParams []ast.Obj, checkDeclared bool) glob.GlobRet {
	if len(params) != len(setParams) {
		return glob.ErrRet(fmt.Errorf("number of params and set params are not the same"))
	}

	// 检查所有参数都声明了
	paramSet := map[string]struct{}{}
	for i, param := range params {
		_, ok := paramSet[param]
		if ok {
			return glob.ErrRet(fmt.Errorf("parameter %s is declared multiple times", param))
		}
		if checkDeclared {
			ret := e.AreAtomsInObjDefined(setParams[i], paramSet)
			if ret.IsErr() {
				ret.AddMsg(fmt.Sprintf("in parameter set for param %s", param))
				return ret
			}
		}
		paramSet[param] = struct{}{} // setParam 不能 包p含它自己
	}

	return glob.TrueRet("")
}

func (e *Env) NonDuplicateParam_NoUndeclaredParamSet_ExtraAtomNames(params []string, setParams []ast.Obj, extraAtomNames map[string]struct{}, checkDeclared bool) glob.GlobRet {
	if len(params) != len(setParams) {
		return glob.ErrRet(fmt.Errorf("number of params and set params are not the same"))
	}

	// 检查所有参数都声明了
	paramSet := glob.CopyMap(extraAtomNames)
	for i, param := range params {
		_, ok := paramSet[param]
		if ok {
			return glob.ErrRet(fmt.Errorf("parameter %s is declared multiple times", param))
		}
		if checkDeclared {
			ret := e.AreAtomsInObjDefined(setParams[i], paramSet)
			if ret.IsErr() {
				ret.AddMsg(fmt.Sprintf("in parameter set for param %s", param))
				return ret
			}
		}
		paramSet[param] = struct{}{} // setParam 不能 包含它自己
	}

	return glob.TrueRet("")
}
