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

package litex_pipeline

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	exe "golitex/executor"
	kernelLibLitexCode "golitex/kernel_litex_code"
	pkgMgr "golitex/package_manager"
)

func NewBuiltinEnvMgr(envPkgMgr *env.EnvPkgMgr) (*env.EnvMgr, error) {
	curEnvMgr := env.NewEnvMgr(envPkgMgr, []env.EnvMemory{*env.NewEnvMemory()}, make(map[string]*ast.DefLetStmt), make(map[string]*ast.DefPropStmt), make(map[string]*ast.DefExistPropStmt), make(map[string]*ast.DefFnSetStmt), make(map[string]*ast.DefAlgoStmt), make(map[string]*ast.DefProveAlgoStmt))
	curEnvMgr.Init()
	err := useHardcodedCodeToInitEnvMgr(curEnvMgr)
	if err != nil {
		panic(err)
	}
	return curEnvMgr, nil
}

func useHardcodedCodeToInitEnvMgr(envMgr *env.EnvMgr) error {
	pkgPathNameMgr := pkgMgr.NewEmptyPkgMgr()
	statements, err := ast.ParseSourceCode(kernelLibLitexCode.PipelineInitCode, pkgPathNameMgr)
	if err != nil {
		return err
	}

	executor := exe.NewExecutor(envMgr)
	for _, statement := range statements {
		execState := executor.Stmt(statement)
		if execState.IsUnknown() || execState.IsErr() {
			return fmt.Errorf("failed to init pipeline: %s\n%s", err, execState.String())
		}
	}

	return nil
}
