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
)

func (e *Env) IsFcAtomDeclaredByUser(fcAtomName ast.FcAtom) bool {
	for env := e; env != nil; env = env.Parent {
		ok := env.isFcAtomDeclaredAtCurEnv(fcAtomName)
		if ok {
			return true
		}
	}
	return false
}

// 其实最好要分类：有可能是obj，有可能是prop，不能在验证obj的时候验证是prop
func (e *Env) isFcAtomDeclaredAtCurEnv(fcAtomName ast.FcAtom) bool {
	_, ok := e.PropDefMem[string(fcAtomName)]
	if ok {
		return true
	}

	_, ok = e.ExistPropDefMem[string(fcAtomName)]
	if ok {
		return true
	}

	_, ok = e.ObjDefMem[string(fcAtomName)]
	if ok {
		return true
	}

	// _, ok = e.FnTemplateDefMem[string(fcAtomName)]
	_, ok = e.FnTemplateDefMem[string(fcAtomName)]

	return ok
}

func (e *Env) isAtomObj(atom ast.FcAtom) bool {
	_, ok := ast.IsNumLitFcAtom(atom)
	if ok {
		return true
	}

	_, ok = glob.BuiltinObjKeywordSet[string(atom)]
	if ok {
		return true
	}

	return e.isUserDefinedObj(atom)
}

func (e *Env) AtomsAreObj(atomSlice []ast.FcAtom) bool {
	for _, atom := range atomSlice {
		if !e.isAtomObj(atom) {
			return false
		}
	}
	return true
}

func (e *Env) AreAtomsInFcAreDeclared(fc ast.Fc, extraAtomNames map[string]struct{}) bool {
	atoms := ast.GetAtomsInFc(fc)
	return e.AreAtomsDeclared(atoms, extraAtomNames)
}

// TODO 来自上层的时候，有时候如果fact是uniFact，那传来的extraAtomNames里已经有uniParam了，这其实是浪费计算了
func (e *Env) AreAtomsInFactAreDeclared(fact ast.FactStmt, extraAtomNames map[string]struct{}) bool {
	switch asStmt := fact.(type) {
	case *ast.UniFactStmt:
		for _, param := range asStmt.Params {
			extraAtomNames[param] = struct{}{}
		}
		for _, dom := range asStmt.DomFacts {
			ok := e.AreAtomsInFactAreDeclared(dom, extraAtomNames)
			if !ok {
				return false
			}
		}
		for _, then := range asStmt.ThenFacts {
			ok := e.AreAtomsInFactAreDeclared(then, extraAtomNames)
			if !ok {
				return false
			}
		}
		return true
	case *ast.UniFactWithIffStmt:
		for _, param := range asStmt.UniFact.Params {
			extraAtomNames[param] = struct{}{}
		}
		for _, dom := range asStmt.UniFact.DomFacts {
			ok := e.AreAtomsInFactAreDeclared(dom, extraAtomNames)
			if !ok {
				return false
			}
		}

		for _, then := range asStmt.UniFact.ThenFacts {
			ok := e.AreAtomsInFactAreDeclared(then, extraAtomNames)
			if !ok {
				return false
			}
		}

		for _, iff := range asStmt.IffFacts {
			ok := e.AreAtomsInFactAreDeclared(iff, extraAtomNames)
			if !ok {
				return false
			}
		}
		return true
	case *ast.IntensionalSetStmt:
		atoms := fact.GetAtoms()
		extraAtomNames[asStmt.Param] = struct{}{}
		return e.AreAtomsDeclared(atoms, extraAtomNames)
	default:
		atoms := fact.GetAtoms()
		return e.AreAtomsDeclared(atoms, extraAtomNames)
	}
}

func (e *Env) AreAtomsDeclared(atoms []ast.FcAtom, extraAtomNames map[string]struct{}) bool {
	for _, atom := range atoms {
		if !e.IsAtomDeclared(atom, extraAtomNames) {
			return false
		}
	}
	return true
}

func (e *Env) IsAtomDeclared(atom ast.FcAtom, extraAtomNames map[string]struct{}) bool {
	// 如果是内置的符号，那就声明了
	if glob.IsBuiltinKeywordKeySymbolCanBeFcAtomName(string(atom)) {
		return true
	}

	// 如果是数字，那就声明了
	if _, ok := ast.IsNumLitFcAtom(atom); ok {
		return true
	}

	ok := e.IsFcAtomDeclaredByUser(atom)
	if ok {
		return true
	}

	_, ok = extraAtomNames[string(atom)]
	// if ok && atom.PkgName == glob.EmptyPkg {
	// if ok {
	// 	return true
	// }

	// return false
	return ok
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

func (e *Env) NonDuplicateParam_NoUndeclaredParamSet_ExtraAtomNames(params []string, setParams []ast.Fc, extraAtomNames map[string]struct{}, checkDeclared bool) error {
	if len(params) != len(setParams) {
		return fmt.Errorf("number of params and set params are not the same")
	}

	// 检查所有参数都声明了
	paramSet := glob.CopyMap(extraAtomNames)
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
