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
	env "golitex/environment"
	exe "golitex/executor"
	kernelLibLitexCode "golitex/kernel_litex_code"
	parser "golitex/parser"
)

func GetEnvWithBuiltinParentEnv() (*env.Env, error) {
	curEnv := env.NewEnv(nil)
	curEnv.Init()
	err := useHardcodedCodeToInit(curEnv)
	if err != nil {
		panic(err)
	}
	curEnv = env.NewEnv(curEnv)
	return curEnv, nil
}

func useHardcodedCodeToInit(env *env.Env) error {
	statements, err := parser.ParseSourceCode(kernelLibLitexCode.PipelineInitCode)
	if err != nil {
		return err
	}

	executor := exe.NewExecutor(env)
	for _, statement := range statements {
		execState := executor.Stmt(statement)
		if execState.IsUnknown() || execState.IsErr() {
			return fmt.Errorf("failed to init pipeline: %s\n%s", err, execState.String())
		}
	}

	return nil
}
