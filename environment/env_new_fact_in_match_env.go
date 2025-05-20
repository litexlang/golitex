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
)

func (env *Env) NewFactInMatchEnv(stmt ast.FactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.storeSpecFactInMem(f)
	case *ast.LogicExprStmt:
		return env.storeLogicFact(f)
	case *ast.UniFactStmt:
		return env.newFactInMatchEnv_UniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) storeSpecFactInMem(stmt *ast.SpecFactStmt) error {
	var knownFactsStructPtr *KnownFactsStruct
	var ok bool

	if env.CurMatchEnv != nil {
		envFact := &env.CurMatchEnv.Fact
		knownFactsStructPtr, ok = env.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
			env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
		}
	} else {
		knownFactsStructPtr = &env.KnownFacts
	}

	err := knownFactsStructPtr.SpecFactMem.newFact(stmt, env.CurMatchEnv)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) storeLogicFact(stmt *ast.LogicExprStmt) error {
	var knownFactsStructPtr *KnownFactsStruct
	var ok bool

	if env.CurMatchEnv != nil {
		envFact := &env.CurMatchEnv.Fact
		knownFactsStructPtr, ok = env.GetFactsFromKnownFactInMatchEnv(envFact)
		if !ok {
			env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
			env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
		}
	} else {
		knownFactsStructPtr = &env.KnownFacts
	}

	err := knownFactsStructPtr.SpecFactInLogicExprMem.newFact(stmt, env.CurMatchEnv)
	if err != nil {
		return nil
	}

	return nil
}

func (env *Env) newFactInMatchEnv_UniFact(stmt *ast.UniFactStmt) error {
	_ = stmt
	return nil
}
