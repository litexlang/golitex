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

func (env *Env) NewFactInMatchEnv(stmt ast.FactStmt, envFact *ast.SpecFactStmt) error {
	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newFactInMatchEnv_SpecFact(f, envFact)
	case *ast.LogicExprStmt:
		return env.newFactInMatchEnv_LogicExpr(f, envFact)
	case *ast.UniFactStmt:
		return env.newFactInMatchEnv_UniFact(f, envFact)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) newFactInMatchEnv_SpecFact(stmt *ast.SpecFactStmt, envFact *ast.SpecFactStmt) error {
	knownFactsStructPtr, ok := env.GetFactsFromKnownFactInMatchEnv(envFact)
	if !ok {
		env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
		env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
	}

	err := knownFactsStructPtr.SpecFactMem.NewFact(stmt, envFact)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) newFactInMatchEnv_LogicExpr(stmt *ast.LogicExprStmt, envFact *ast.SpecFactStmt) error {
	knownFactsStructPtr, ok := env.GetFactsFromKnownFactInMatchEnv(envFact)
	if !ok {
		env.KnownFactInMatchEnv[envFact.PropName.PkgName] = make(map[string]KnownFactsStruct)
		env.KnownFactInMatchEnv[envFact.PropName.PkgName][envFact.PropName.Name] = makeKnownFactsStruct()
	}

	err := knownFactsStructPtr.SpecFactInLogicExprMem.NewFact(stmt, envFact)
	if err != nil {
		return nil
	}

	return nil
}

func (env *Env) newFactInMatchEnv_UniFact(stmt *ast.UniFactStmt, envFact *ast.SpecFactStmt) error {
	return nil
}
