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

package litex_pipeline

import (
	"fmt"
	env "golitex/environment"
	exe "golitex/executor"
	glob "golitex/glob"
	kernelLib "golitex/kernel_lib"
	parser "golitex/parser"
)

func pipelineExecutorInit() (*exe.Executor, error) {
	glob.IsRunningPipelineInit = true
	defer func() {
		glob.IsRunningPipelineInit = false
	}()

	curEnv := env.NewEnv(nil)
	curEnv.Init()
	executor := exe.NewExecutor(curEnv)
	executor.NewEnv(curEnv)
	err := useHardcodedCodeToInit(executor)
	if err != nil {
		return nil, err
	}
	return executor, nil
}

func useHardcodedCodeToInit(executor *exe.Executor) error {
	statements, err := parser.ParseSourceCode(kernelLib.PipelineInitCode)
	if err != nil {
		return err
	}
	for _, statement := range statements {
		execState, err := executor.Stmt(statement)
		if err != nil || execState != glob.ExecState_True {
			return fmt.Errorf("failed to init pipeline: %s", err)
		}
	}

	executor.ClearMsgs()

	return nil
}
