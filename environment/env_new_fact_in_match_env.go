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
	err := env.KnownFactsStruct.SpecFactMem.newFact(stmt)
	if err != nil {
		return err
	}

	return nil
}

func (env *Env) storeLogicFact(stmt *ast.OrStmt) error {
	err := env.KnownFactsStruct.SpecFactInLogicExprMem.newFact(stmt)
	if err != nil {
		return nil
	}

	return nil
}

func (env *Env) storeUniFact(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) error {
	err := env.KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
	if err != nil {
		return err
	}

	return nil
}
