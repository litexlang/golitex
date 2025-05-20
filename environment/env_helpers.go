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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (e *Env) GetFactsFromKnownFactInMatchEnv(envFact *ast.SpecFactStmt) (*KnownFactsStruct, bool) {
	knownFacts, ok := e.KnownFactInMatchEnv.Get(envFact.PropName.PkgName, envFact.PropName.Name)
	if !ok {
		return nil, false
	}
	return &knownFacts, true
}

// Commutative Prop

func (e *Env) insertCommutativeProp(propName ast.FcAtom) {
	if _, ok := e.CommutativeProp[propName.PkgName]; !ok {
		e.CommutativeProp[propName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.CommutativeProp[propName.PkgName][propName.Name]; !ok {
		e.CommutativeProp[propName.PkgName][propName.Name] = struct{}{}
	}
}

func (e *Env) IsCommutativeProp(propName ast.FcAtom) bool {
	if ast.IsFcAtomWithName(&propName, glob.KeySymbolEqual) {
		return true
	}

	if _, ok := e.CommutativeProp[propName.PkgName][propName.Name]; ok {
		return true
	}
	return false
}

// End of Commutative Prop

// Commutative Fn

func (e *Env) InsertCommutativeFn(fnName ast.FcAtom) {
	if _, ok := e.CommutativeFn[fnName.PkgName]; !ok {
		e.CommutativeFn[fnName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.CommutativeFn[fnName.PkgName][fnName.Name]; !ok {
		e.CommutativeFn[fnName.PkgName][fnName.Name] = struct{}{}
	}
}

func (e *Env) IsCommutativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolStar) {
		return true
	}

	if _, ok := e.CommutativeFn[fnName.PkgName][fnName.Name]; ok {
		return true
	}
	return false
}

// End of Commutative Fn

// Associative Fn

func (e *Env) InsertAssociativeFn(fnName ast.FcAtom) {
	if _, ok := e.AssociativeFn[fnName.PkgName]; !ok {
		e.AssociativeFn[fnName.PkgName] = make(map[string]struct{})
	}
	if _, ok := e.AssociativeFn[fnName.PkgName][fnName.Name]; !ok {
		e.AssociativeFn[fnName.PkgName][fnName.Name] = struct{}{}
	}
}

func (e *Env) IsAssociativeFn(fnName ast.FcAtom) bool {
	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolPlus) {
		return true
	}

	if ast.IsFcAtomWithName(&fnName, glob.KeySymbolStar) {
		return true
	}

	if _, ok := e.AssociativeFn[fnName.PkgName][fnName.Name]; ok {
		return true
	}
	return false
}

// End of Associative Fn
