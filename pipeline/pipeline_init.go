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
	env "golitex/environment"
	exe "golitex/executor"
	parser "golitex/parser"
)

func pipelineExecutorInit() (*exe.Executor, error) {
	curEnv := env.NewEnv(nil, nil)
	curEnv.Init()
	executor := exe.NewExecutor(curEnv)
	err := useHardcodedCodeToInit(executor)
	if err != nil {
		return nil, err
	}
	return executor, nil
}

func useHardcodedCodeToInit(executor *exe.Executor) error {
	code := `
prop last_two_objects_are_equal(x, y, y2 obj):
	y = y2

know prop larger_is_transitive(x, y, z R):
	x > y
	y > z

know forall x, y, z R:
	$larger_is_transitive(x, y, z)
	then:
		x > z
		`

	statements, err := parser.ParseSourceCode(code)
	if err != nil {
		return err
	}
	for _, statement := range statements {
		_, err := executor.Stmt(statement)
		if err != nil {
			return err
		}
	}
	return nil
}
