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

func NewBuiltinEnvMgrWithNewEmptyEnv(envPkgMgr *env.EnvPkgMgr) (*env.EnvMgr, error) {
	var err error
	if env.BuiltinEnvMgr == nil {
		env.BuiltinEnvMgr, err = NewBuiltinEnvMgr(envPkgMgr)
		if err != nil {
			return nil, err
		}
	}

	envMgr := env.CopyEnvMgr_SharePkgMgr(env.BuiltinEnvMgr)
	envMgr = envMgr.NewEnv()
	return envMgr, nil
}

func NewBuiltinEnvMgr(envPkgMgr *env.EnvPkgMgr) (*env.EnvMgr, error) {
	curEnvMgr := env.NewEnvMgr(envPkgMgr, []env.EnvMemory{*env.NewEnvMemory()}, make(map[string]struct{}), make(map[string]*ast.DefPropStmt), make(map[string]*ast.DefExistPropStmt), make(map[string]*ast.DefFnSetStmt), make(map[string]*ast.DefAlgoStmt), make(map[string]*ast.DefProveAlgoStmt))
	curEnvMgr.Init()
	err := useHardcodedCodeToInitEnvMgr(curEnvMgr)
	if err != nil {
		panic(err)
	}

	for k := range curEnvMgr.AllDefinedAlgoNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}
	for k := range curEnvMgr.AllDefinedPropNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}
	for k := range curEnvMgr.AllDefinedExistPropNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}
	for k := range curEnvMgr.AllDefinedFnSetNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}
	for k := range curEnvMgr.AllDefinedAtomObjNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}
	for k := range curEnvMgr.AllDefinedProveAlgoNames {
		ast.BuiltinAndKernelDefinedNames[k] = struct{}{}
	}

	return curEnvMgr, nil
}

func useHardcodedCodeToInitEnvMgr(envMgr *env.EnvMgr) error {
	pkgPathNameMgr := pkgMgr.NewEmptyPkgMgr()

	// statements, err := ast.ParseSourceCode(kernelLibLitexCode.PipelineInitCode, pkgPathNameMgr)

	blocks, err := ast.PreprocessAndMakeSourceCodeIntoBlocks(kernelLibLitexCode.PipelineInitCode)
	if err != nil {
		return err
	}

	p := ast.NewTbParser(pkgPathNameMgr)
	executor := exe.NewExecutor(envMgr)

	for _, block := range blocks {
		topStmt, err := p.Stmt(&block)
		if err != nil {
			return err
		}
		execState := executor.Stmt(topStmt)
		if execState.IsUnknown() || execState.IsErr() {
			return fmt.Errorf("failed to init pipeline: %s\n%s", err, execState.String())
		}
	}

	return nil
}
