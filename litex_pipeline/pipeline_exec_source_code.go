// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_pipeline

import (
	env "golitex/litex_env"
	exe "golitex/litex_executor"
	parser "golitex/litex_parser"
	"strings"
)

func ExecuteCodeAndReturnMessage(code string) (string, error) {
	msgOfTopStatements, err := executeCodeAndReturnMessageSlice(code)
	if err != nil {
		return "", err
	}
	ret := strings.Join(msgOfTopStatements, "\n\n\n")
	return ret, nil
}

func executeCodeAndReturnMessageSlice(code string) ([]string, error) {
	topStmtSlice, err := parser.ParseSourceCode(code)
	if err != nil {
		return nil, err
	}
	curEnv := env.NewEnv(nil, nil, "")
	executor := *exe.NewExecutor(curEnv)

	msgOfTopStatements := []string{}

	for _, topStmt := range topStmtSlice {
		err := executor.TopLevelStmt(&topStmt)
		if err != nil {
			return nil, err
		}
		msgOfTopStatements = append(msgOfTopStatements, executor.GetMsgAsStr0ToEnd())
	}

	return msgOfTopStatements, nil
}
