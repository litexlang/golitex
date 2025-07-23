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

func (e *Env) GetLatestFnTemplate(fn ast.Fc) (*ast.FnTemplateStmt, bool) {
	for env := e; env != nil; env = env.Parent {
		fnDef, ok := env.FnInFnTemplateFactsMem[fn.String()]
		if ok {
			return fnDef[len(fnDef)-1], true
		}
	}
	return nil, false
}

func (memory FnInFnTemplateTemplateFactsMem) insert(fc ast.Fc, templateWhereFcIs *ast.FcFn) error {
	fnDefs, ok := memory[fc.String()]
	if !ok {
		memory[fc.String()] = []*ast.FcFn{templateWhereFcIs}
		return nil
	} else {
		fnDefs = append(fnDefs, templateWhereFcIs)
		memory[fc.String()] = fnDefs
		return nil
	}
}

func (memory FnInFnTemplateFactsMem) insert(fc ast.Fc, stmt *ast.FnTemplateStmt) error {
	fnDefs, ok := memory[fc.String()]
	if !ok {
		memory[fc.String()] = []*ast.FnTemplateStmt{stmt}
		return nil
	}

	fnDefs = append(fnDefs, stmt)
	memory[fc.String()] = fnDefs

	return nil
}

func (e *Env) GetFnTemplateOfFc(fn ast.Fc) ([]*ast.FnTemplateStmt, bool) {
	fnDefs := []*ast.FnTemplateStmt{}
	for env := e; env != nil; env = env.Parent {
		fnDefsFromEnv, ok := env.FnInFnTemplateFactsMem[fn.String()]
		if ok {
			fnDefs = append(fnDefs, fnDefsFromEnv...)
		}
	}
	if len(fnDefs) == 0 {
		return nil, false
	}
	return fnDefs, true
}
