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
		return env.newSpecFact(f)
	case *ast.LogicExprStmt:
		return env.newLogicExprStmt(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	default:
		return fmt.Errorf("unknown fact type: %T", stmt)
	}
}

func (env *Env) NewFactInMatchEnv_SpecFact(stmt *ast.SpecFactStmt) error {
	_ = stmt
	return nil
}

func (env *Env) NewFactInMatchEnv_LogicExpr(stmt *ast.LogicExprStmt) error {
	_ = stmt
	return nil
}

func (env *Env) NewFactInMatchEnv_UniFact(stmt *ast.UniFactStmt) error {
	_ = stmt
	return nil
}
