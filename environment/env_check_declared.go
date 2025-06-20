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

func (e *Env) AreAtomsInFcAreDeclared(fc ast.Fc, extraAtomNames map[string]struct{}) bool {
	atoms := ast.GetAtomsInFc(fc)
	return e.AreAtomsDeclared(atoms, extraAtomNames)
}

// TODO 来自上层的时候，有时候如果fact是uniFact，那传来的extraAtomNames里已经有uniParam了，这其实是浪费计算了
func (e *Env) AreAtomsInFactAreDeclared(fact ast.FactStmt, extraAtomNames map[string]struct{}) bool {
	atoms := fact.GetAtoms()

	if asUniFact, ok := fact.(*ast.UniFactStmt); ok {
		for _, param := range asUniFact.Params {
			extraAtomNames[param] = struct{}{}
		}
	} else if asUniFactIff, ok := fact.(*ast.UniFactWithIffStmt); ok {
		for _, param := range asUniFactIff.UniFact.Params {
			extraAtomNames[param] = struct{}{}
		}
	}

	ok := e.AreAtomsDeclared(atoms, extraAtomNames)
	if !ok {
		return false
	}
	return ok
}

func (e *Env) AreAtomsDeclared(atoms []*ast.FcAtom, extraAtomNames map[string]struct{}) bool {
	for _, atom := range atoms {
		if !e.IsAtomDeclared(atom, extraAtomNames) {
			return false
		}
	}
	return true
}

func (e *Env) IsAtomDeclared(atom *ast.FcAtom, extraAtomNames map[string]struct{}) bool {
	// 如果是内置的符号，那就声明了
	if glob.IsBuiltinKeywordKeySymbolCanBeFcAtomName(atom.Name) {
		return true
	}

	// 如果是数字，那就声明了
	if _, ok := ast.IsNumLitFcAtom(atom); ok {
		return true
	}

	_, ok := e.GetFcAtomDef(atom)
	if ok {
		return true
	}

	_, ok = extraAtomNames[atom.Name]
	if ok && atom.PkgName == glob.EmptyPkg {
		return true
	}

	return false
}

func (e *Env) NonDuplicateParam_NoUndeclaredParamSet(params []string, setParams []ast.Fc, checkDeclared bool) error {
	if len(params) != len(setParams) {
		return fmt.Errorf("number of params and set params are not the same")
	}

	// 检查所有参数都声明了
	paramSet := map[string]struct{}{}
	for i, param := range params {
		_, ok := paramSet[param]
		if ok {
			return fmt.Errorf("parameter %s is declared multiple times", param)
		}
		if checkDeclared {
			ok = e.AreAtomsInFcAreDeclared(setParams[i], paramSet)
			if !ok {
				return fmt.Errorf(AtomsInFcNotDeclaredMsg(setParams[i]))
			}
		}
		paramSet[param] = struct{}{} // setParam 不能 包含它自己
	}

	return nil
}
