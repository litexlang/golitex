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
	"fmt"
	ast "golitex/ast"
)

func (e *Env) inFactPostProcess(fact *ast.SpecFactStmt) error {
	if len(fact.Params) != 2 {
		return fmt.Errorf("in fact expect 2 parameters, get %d in %s", len(fact.Params), fact.String())
	}

	if isTemplate, err := e.inFactPostProcess_InFnTemplate(fact); isTemplate {
		return err
	}

	return nil
}

func (e *Env) inFactPostProcess_InFnTemplate(fact *ast.SpecFactStmt) (bool, error) {
	templateName, ok := fact.Params[1].(*ast.FcAtom)
	if !ok {
		return false, nil
	}

	curInTemplate, ok := e.GetLatestFnTemplate(templateName)
	if !ok {
		return false, nil
	}

	_ = curInTemplate

	panic("")
}
