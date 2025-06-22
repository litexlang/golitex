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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	ast "golitex/ast"
)

func (env *Env) storeSpecFactInMem(stmt *ast.SpecFactStmt) error {
	var knownFactsStructPtr *KnownFactsStruct
	var ok bool

	if env.CurMatchProp != nil {
		envFact := env.CurMatchProp
		knownFactsStructPtr, ok = env.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
			env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
			knownFactsStruct := env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name]
			knownFactsStructPtr = &knownFactsStruct
		}
	} else {
		knownFactsStructPtr = &env.KnownFactsStruct
	}

	err := knownFactsStructPtr.SpecFactMem.newFact(stmt, env.CurMatchProp)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) storeLogicFact(stmt *ast.OrStmt) error {
	var knownFactsStructPtr *KnownFactsStruct
	var ok bool

	if env.CurMatchProp != nil {
		envFact := env.CurMatchProp
		knownFactsStructPtr, ok = env.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
			env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
			knownFactsStruct := env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name]
			knownFactsStructPtr = &knownFactsStruct
		}
	} else {
		knownFactsStructPtr = &env.KnownFactsStruct
	}

	err := knownFactsStructPtr.SpecFactInLogicExprMem.newFact(stmt, env.CurMatchProp)
	if err != nil {
		return nil
	}

	return nil
}

func (env *Env) storeUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) error {
	var knownFactsStructPtr *KnownFactsStruct
	var ok bool

	if env.CurMatchProp != nil {
		envFact := env.CurMatchProp
		knownFactsStructPtr, ok = env.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
			env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
			knownFactsStruct := env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name]
			knownFactsStructPtr = &knownFactsStruct
		}
	} else {
		knownFactsStructPtr = &env.KnownFactsStruct
	}

	err := knownFactsStructPtr.SpecFactInUniFactMem.newFact(specFact, uniFact, env.CurMatchProp)
	if err != nil {
		return err
	}

	return nil
}
